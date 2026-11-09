"""Explicit certificate annotations; these never participate in truth closure."""


def validate_comparisons(result, statements, definitions):
    cells = result.get('research_comparisons', [])
    if not isinstance(cells, list):
        raise ValueError('research_comparisons must be a list')
    seen = set()
    for cell in cells:
        if not isinstance(cell, dict):
            raise ValueError('comparison must be an object')
        for field in ('target_statement_id', 'rival_statement_id'):
            if not isinstance(cell.get(field), str) or cell[field] not in statements:
                raise ValueError(f'{field} must name a known statement')
        if not isinstance(cell.get('sense_definition_id'), str) or cell['sense_definition_id'] not in definitions:
            raise ValueError('sense_definition_id must name a known definition')
        key = tuple(cell[field] for field in ('target_statement_id', 'rival_statement_id', 'sense_definition_id'))
        if key in seen:
            raise ValueError('duplicate comparison cell in result')
        seen.add(key)
        if cell.get('outcome') not in ('excluded', 'model-witnessed', 'unresolved', 'untested'):
            raise ValueError('invalid comparison outcome')
        if cell['outcome'] in ('excluded', 'model-witnessed') and result.get('transcription'):
            raise ValueError('checked comparisons require a non-transcription result')
        for field in ('conditions', 'scope', 'coverage', 'exclusivity', 'next_step'):
            if not isinstance(cell.get(field), str) or not cell[field].strip():
                raise ValueError(f'comparison requires explicit {field}')
        if cell['outcome'] == 'model-witnessed' and (not isinstance(cell.get('witness'), str) or not cell['witness'].strip()):
            raise ValueError('model-witnessed comparison requires exact witness description')
        if cell['outcome'] == 'unresolved' and (not isinstance(cell.get('gap'), str) or not cell['gap'].strip()):
            raise ValueError('unresolved comparison requires exact gap')

        for field in ('witness', 'gap'):
            if field in cell and (not isinstance(cell[field], str) or not cell[field].strip()):
                raise ValueError(f'{field} must be a non-empty string')
