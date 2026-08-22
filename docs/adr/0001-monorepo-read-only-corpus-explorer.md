# Keep the first Corpus Explorer in a monorepo and read directly from corpus records

Truth Core will add its first web application as an isolated app in a monorepo, so later web applications can live beside it without entangling their concerns. The Explorer is a read-only, build-time view of the canonical `corpus/` records rather than a second database or editorial system; this preserves the corpus as the source of scholarly truth and keeps the MVP narrowly scoped.
