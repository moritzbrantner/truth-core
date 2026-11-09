"""Acquire official release assets; credentials are sent only to api.github.com."""
import argparse
import http.client
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args):
        return None


OPENER = urllib.request.build_opener(NoRedirect)
CDN_HOSTS = {'release-assets.githubusercontent.com', 'objects.githubusercontent.com'}


def fetch(url, target, binary=False):
    """Bounded streaming attempts; a failed attempt never leaves partial output."""
    token = os.environ['GH_TOKEN']
    if not token:
        raise ValueError('GitHub Actions token is required')
    initial = urllib.parse.urlsplit(url)
    if initial.scheme != 'https' or initial.netloc != 'api.github.com':
        raise ValueError('Acquisition must start at the GitHub REST API')
    for attempt in range(4):
        current = url
        try:
            for _ in range(5):
                host = urllib.parse.urlsplit(current)
                if host.scheme != 'https' or host.netloc not in {'api.github.com', *CDN_HOSTS}:
                    raise ValueError('Unapproved release redirect host')
                headers = {'Accept': 'application/octet-stream' if binary else 'application/vnd.github+json',
                           'User-Agent': 'truth-core-ci', 'X-GitHub-Api-Version': '2022-11-28'}
                if host.netloc == 'api.github.com':
                    headers['Authorization'] = 'Bearer ' + token
                try:
                    response = OPENER.open(urllib.request.Request(current, headers=headers), timeout=60)
                except urllib.error.HTTPError as error:
                    if error.code == 302 and binary:
                        current = urllib.parse.urljoin(current, error.headers['Location'])
                        error.close()
                        continue
                    raise
                with response, target.open('wb') as output:
                    deadline = time.monotonic() + 600
                    while chunk := response.read(1024 * 1024):
                        if time.monotonic() > deadline:
                            raise TimeoutError('Release transfer deadline exceeded')
                        output.write(chunk)
                return
            raise ValueError('Too many release redirects')
        except urllib.error.HTTPError as error:
            error.close()
            target.unlink(missing_ok=True)
            if error.code not in {429, 500, 502, 503, 504} or attempt == 3:
                raise RuntimeError(f'GitHub release acquisition failed: HTTP {error.code}') from None
        except (urllib.error.URLError, TimeoutError, ConnectionError, http.client.IncompleteRead) as error:
            target.unlink(missing_ok=True)
            if attempt == 3:
                raise RuntimeError('GitHub release acquisition exhausted transport retries') from None
        print(f'Retrying transient release acquisition (attempt {attempt + 2}/4)', flush=True)
        time.sleep(2 ** (attempt + 1))


def release(repo, tag):
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / 'release.json'
        route = 'latest' if tag == 'latest' else 'tags/' + urllib.parse.quote(tag, safe='')
        fetch(f'https://api.github.com/repos/{repo}/releases/{route}', path)
        data = json.loads(path.read_text())
    if not isinstance(data, dict) or not isinstance(data.get('assets'), list):
        raise ValueError('Malformed GitHub release metadata')
    if data.get('draft') or data.get('prerelease') or not re.fullmatch(r'(?:bun-)?v\d+\.\d+\.\d+', data.get('tag_name', '')):
        raise ValueError('Expected a stable versioned release')
    if tag != 'latest' and data['tag_name'] != tag:
        raise ValueError('Release does not match requested pin')
    return data


def asset(data, name):
    matches = [a for a in data['assets'] if a.get('name') == name]
    if len(matches) != 1:
        raise ValueError(f'Expected exactly one official asset: {name}')
    a = matches[0]
    if type(a.get('id')) is not int or a['id'] <= 0 or a.get('size', 0) <= 0 or a.get('state') != 'uploaded':
        raise ValueError('Malformed release asset')
    return a['id']


def plan(tool):
    if platform.system() != 'Linux':
        raise ValueError('Only the current Linux CI runners are supported')
    arch = {'x86_64': 'x86_64', 'aarch64': 'aarch64'}.get(platform.machine())
    if not arch:
        raise ValueError('Unsupported CI runner architecture')
    if tool == 'bun':
        data = release('oven-sh/bun', 'latest')
        # Baseline works on x64 runners without requiring AVX2.
        name = 'bun-linux-x64-baseline.zip' if arch == 'x86_64' else 'bun-linux-aarch64.zip'
        return {'tool': tool, 'version': data['tag_name'], 'assets': [
            {'repo': 'oven-sh/bun', 'id': asset(data, name), 'name': name}]}
    pin = Path('lean-toolchain').read_text().strip()
    if not re.fullmatch(r'leanprover/lean4:v\d+\.\d+\.\d+', pin):
        raise ValueError('Expected an exact stable leanprover/lean4 pin')
    tag = pin.split(':')[1]
    lean = release('leanprover/lean4', tag)
    elan = release('leanprover/elan', 'latest')
    lean_name = f'lean-{tag[1:]}-linux' + ('_aarch64' if arch == 'aarch64' else '') + '.tar.zst'
    elan_name = f'elan-{arch}-unknown-linux-gnu.tar.gz'
    return {'tool': tool, 'version': tag, 'pin': pin, 'elan': elan['tag_name'], 'assets': [
        {'repo': 'leanprover/elan', 'id': asset(elan, elan_name), 'name': elan_name},
        {'repo': 'leanprover/lean4', 'id': asset(lean, lean_name), 'name': lean_name}]}


def install(config, root):
    root.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        for item in config['assets']:
            archive = tmp / item['name']
            fetch(f"https://api.github.com/repos/{item['repo']}/releases/assets/{item['id']}", archive, True)
            if item['repo'] == 'oven-sh/bun':
                subprocess.run(['unzip', '-q', str(archive), '-d', str(tmp / 'bun')], check=True)
                (root / 'bin').mkdir(exist_ok=True)
                shutil.copy2(next((tmp / 'bun').glob('*/bun')), root / 'bin/bun')
                (root / 'bin/bun').chmod(0o755)
            elif item['repo'] == 'leanprover/elan':
                subprocess.run(['tar', '-xzf', str(archive), '-C', str(tmp)], check=True)
                subprocess.run([str(tmp / 'elan-init'), '-y', '--default-toolchain', 'none', '--no-modify-path'], check=True)
            else:
                # Elan's canonical directory encoding; no override of lean-toolchain.
                dest = root / 'elan/toolchains' / config['pin'].replace('/', '--').replace(':', '---')
                dest.mkdir(parents=True, exist_ok=True)
                subprocess.run(['tar', '--zstd', '-xf', str(archive), '--strip-components=1', '-C', str(dest)], check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('operation', choices=['resolve', 'install', 'validate'])
    parser.add_argument('tool', choices=['lean', 'bun'])
    args = parser.parse_args()
    root = Path.home() / '.cache/truth-core-release' / args.tool
    config_path = Path(os.environ['RUNNER_TEMP']) / f'{args.tool}-release.json'
    if args.operation == 'resolve':
        config = plan(args.tool)
        config_path.write_text(json.dumps(config))
        with open(os.environ['GITHUB_OUTPUT'], 'a') as output:
            output.write('version=' + config['version'] + '-' + config.get('elan', '') + '\n')
        return
    config = json.loads(config_path.read_text())
    if args.tool == 'lean':
        os.environ['ELAN_HOME'] = str(root / 'elan')
    if args.operation == 'install':
        install(config, root)
    else:
        bindir = root / ('elan/bin' if args.tool == 'lean' else 'bin')
        os.environ['PATH'] = str(bindir) + os.pathsep + os.environ['PATH']
        expected = config['version'].removeprefix('bun-').removeprefix('v')
        for command in (['lean', 'lake'] if args.tool == 'lean' else ['bun']):
            version = subprocess.check_output([str(bindir / command), '--version'], text=True).strip()
            print(version)
            if not re.search(r'(?<![\d.])' + re.escape(expected) + r'(?![\d.])', version):
                raise ValueError(f'{command} version differs from resolved release')
        with open(os.environ['GITHUB_PATH'], 'a') as output:
            output.write(str(bindir) + '\n')
        if args.tool == 'lean':
            with open(os.environ['GITHUB_ENV'], 'a') as output:
                output.write('ELAN_HOME=' + os.environ['ELAN_HOME'] + '\n')


if __name__ == '__main__':
    main()
