# sr-lang Neovim Plugin

Minimal Neovim plugin for experimenting with the Tree-sitter grammar bundled with this repository.

## Installation

Use your preferred plugin manager or a plain git checkout. For example, with the built-in package manager:

```bash
mkdir -p ~/.config/nvim/pack/sr/start
ln -s $(pwd) ~/.config/nvim/pack/sr/start/sr-lang
```

## Setup

Add the following to your `init.lua` or `init.vim`:

```lua
require('sr').setup()
```

When you open an `.sr` file, Neovim will automatically register the grammar from `tools/tree-sitter-sr`. The parser can be compiled via:

```vim
:TSInstallFromGrammar sr
```

The plugin also registers a basic highlight query for the language.
