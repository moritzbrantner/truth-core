# Use Bun workspaces and Turborepo for web applications

Truth Core will manage its web applications with Bun workspaces and Turborepo. This gives the current Next.js Corpus Explorer and later applications one workspace-level dependency and task boundary, while keeping shared packages optional until they serve more than one app.
