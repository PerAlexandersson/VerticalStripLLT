# Lean MCP routing for the new project

The registered Lean MCP starts in RealRooted. Its read-only local search accepts
an explicit project root, but build/LSP defaults could select the wrong package
or bypass this project's wrapper. Continue using explicit-root searches and
`lake-workspace` checks. If interactive proof work needs diagnostics repeatedly,
request a project-aware registration that preserves the global single-builder
rule; do not silently change the shared MCP registration.
