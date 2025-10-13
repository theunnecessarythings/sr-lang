# tree-sitter-sr

Experimental Tree-sitter grammar for the `sr` programming language.

## Development

> **Note:** Installing dependencies requires contacting the public npm registry for
> the `tree-sitter-cli` package. If you are working in an offline or firewalled
> environment (such as the automated execution environment for this repository), the
> install step will fail. Run the commands below on a machine with network access or
> with the CLI already available on your `PATH`.

```bash
npm install
npx tree-sitter generate
npx tree-sitter test
```

Generated artifacts will be written to `src/` and ignored by git.

## Corpus

Test fixtures live under `corpus/` and should exercise as much of the language syntax as possible.
