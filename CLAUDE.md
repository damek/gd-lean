# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands
- Build project: `lake build`
- Check a file: `lake env lean Gd/Lean/YourFile.lean`
- Watch mode: `lake env lean --watch Gd/Lean/YourFile.lean`

## Project Structure
- `Gd/Lean/*.lean` - Main library files containing formal proofs
- Each file focuses on specific mathematical concepts for gradient descent

## Code Style Guidelines
- **Imports**: Import Mathlib first, then other project files
- **Namespaces**: Open only relevant namespaces (e.g., `open Filter Metric Asymptotics Gradient InnerProductSpace`)
- **Documentation**: Use `--------------------------------------------------------------------------------` with descriptive comments above theorems
- **Theorem Names**: Use CamelCase for theorem names
- **Proofs**: Use structured proofs with `by` tactic blocks
- **Code Blocks**: Separate logical sections with commented dividers using dashes (`----------`)
- **Line Length**: Keep proofs readable with appropriate line breaks
- **Naming Conventions**: Use meaningful variable names representing mathematical concepts