# Dependency Graph

The repository enforces strict import direction:

- `Model` imports only `Model`
- `Semantics` imports `Model` and `Semantics`
- `Validation` imports `Model` and `Semantics`
- `Tests` imports harness + validation/model/semantics as needed

## Layered view

```text
Tests / Apps
    |
Validation
    |
Semantics
    |
  Model
```

## Hard rules

- No file under `TvmLean/Model/` may import `TvmLean/Semantics/` or `TvmLean/Validation/`.
- No file under `TvmLean/Semantics/` may import `TvmLean/Validation/`.
- No `@[extern]` declarations: the model, cryptography included, is pure Lean.

## Enforcement

Lake targets encode the same structure:

- `TvmLeanModel`
- `TvmLeanSemantics`
- `TvmLeanValidation`
- `TvmLeanTests`

A fresh `lake build` defaults to Model + Semantics only.
