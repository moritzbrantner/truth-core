# Use Next.js as the monorepo web platform

The initial Corpus Explorer could be a smaller Vite application, but future Truth Core web applications may benefit from the routing and server-capable conventions of Next.js. The monorepo will therefore use Next.js with static generation for the read-only Explorer, preserving the current no-backend MVP while making Next.js the shared web-platform foundation.
