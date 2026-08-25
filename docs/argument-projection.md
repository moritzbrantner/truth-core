# Argument projection

The corpus model is not a DAG. The React Flow view is a derived projection of selected verified arguments.

- Statements keep independent identity in the corpus.
- Arguments are reusable blocks that can be expanded or collapsed without changing canonical data.
- Expanding a block reveals its premises and inference applications.
- Supporting verified arguments are projected upstream when they conclude one of the expanded block's premises.
- Recursive support is cut at cycles and shown as a back-reference edge rather than recursing forever.
- Layout coordinates, expansion state, and React Flow nodes/edges are UI state only.

The initial projection uses a deliberately simple depth-based layout. A stronger layout engine can replace it later without changing the corpus or projection contract.
