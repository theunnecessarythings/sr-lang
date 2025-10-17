# sr-lang Neovim Plugin

Minimal Neovim plugin for experimenting with the Tree-sitter grammar bundled with this repository. It configures the sr parser for
`nvim-treesitter` and ships Tree-sitter queries for:

- syntax highlighting
- definition-aware locals (`gd`, incremental rename, etc.)
- folding and indentation powered by Tree-sitter

## Installation

Use your preferred plugin manager or a plain git checkout. For example, with the built-in package manager:

```bash
mkdir -p ~/.config/nvim/pack/sr/start
ln -s $(pwd)/tools/nvim-sr ~/.config/nvim/pack/sr/start/sr
```

### lazy.nvim

If you are using [lazy.nvim](https://github.com/folke/lazy.nvim), add the plugin as a local specification and depend on
`nvim-treesitter`:

```lua
{
  dir = vim.fn.expand('~/code/sr-lang/tools/nvim-sr'),
  name = 'sr.nvim',
  dependencies = { 'nvim-treesitter/nvim-treesitter' },
  config = function()
    require('sr').setup()
  end,
}
```

Adjust the `dir` to wherever you have the `sr-lang` repository checked out. If you keep the Tree-sitter grammar elsewhere, pass `grammar_path` to `setup()` (see below).

## Setup

Add the following to your `init.lua` or `init.vim`:

```lua
require('sr').setup()
```

When you open an `.sr` file, Neovim automatically looks for the grammar next to the plugin at `../tree-sitter-sr`. If it is not present, it falls back to the public `sr-lang/tree-sitter-sr` repository.

To compile the parser with `nvim-treesitter` run:

```vim
:TSInstallFromGrammar sr
```

If the grammar lives in a different directory, point the plugin at it explicitly:

```lua
require('sr').setup({ grammar_path = '/path/to/tree-sitter-sr' })
```

Pass any absolute or relative path; the plugin normalizes the location for you. You can also provide a git URL if you prefer pulling the grammar from elsewhere.

With the bundled queries active you should see syntax highlighting, Tree-sitter powered indentation, folding, and symbol-aware motions for sr buffers.
