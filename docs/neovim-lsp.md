# Using the `sr_lang` LSP in Neovim

The `sr_lang` binary exposes a Language Server Protocol implementation behind the `lsp` subcommand. This guide shows how to hook it up to Neovim's built-in LSP client using the lightweight helper that lives in `tools/nvim`.

## 1. Build or install the compiler

The language server is shipped as part of the regular compiler binary. Make sure the `sr_lang` executable that contains your latest changes is accessible on your `PATH`.

```bash
zig build install
export PATH="$(pwd)/zig-out/bin:$PATH"
```

Verify the server can start from the command line:

```bash
sr_lang lsp
```

> The server speaks JSON-RPC over standard input/output and will continue running until it receives `Ctrl+C` or an `exit` request. Neovim launches it with the command shown above.

## 2. Copy the helper plugin

The repository ships a tiny Neovim plugin under [`tools/nvim`](../tools/nvim). You can vendor it into your Neovim configuration or load it through a plugin manager.

With **lazy.nvim** the plugin can be referenced straight from this repository while you iterate locally:

```lua
{
  dir = "/path/to/sr-lang/tools/nvim",
  name = "sr-lang-nvim",
  config = function()
    require("sr_lang").setup()
  end,
}
```

For **packer.nvim** you can do the same:

```lua
use({
  dir = "/path/to/sr-lang/tools/nvim",
  as = "sr-lang-nvim",
  config = function()
    require("sr_lang").setup()
  end,
})
```

If you prefer to vendor the files manually, copy the `lua/` and `ftdetect/` directories into `~/.config/nvim/`.

## 3. Configure optional hooks

`require("sr_lang").setup()` accepts the same options that `vim.lsp.start()` does. The most common hooks are:

```lua
require("sr_lang").setup({
  on_attach = function(client, bufnr)
    -- Enable completion triggered by <c-x><c-o>
    vim.bo[bufnr].omnifunc = "v:lua.vim.lsp.omnifunc"
  end,
  capabilities = require("cmp_nvim_lsp").default_capabilities(),
  settings = {
    ["sr-lang"] = {
      -- future language server settings go here
    },
  },
})
```

You can override the command used to start the server or the filetypes that should attach by passing `cmd = { "path/to/sr_lang", "lsp" }` or `filetypes = { "sr", "srscript" }`.

## 4. Open a `.sr` file

The helper automatically registers the `sr` filetype using Neovim's modern `vim.filetype.add()` API. When you open a buffer ending in `.sr`, the plugin will:

1. Derive a project root by searching upwards for `sr-project.toml`, `sr-project.json`, `srconfig.toml`, or a `.git` directory.
2. Launch (or reuse) a language server instance with `sr_lang lsp` in that root.
3. Attach the client to the current buffer and publish diagnostics as you edit.

Use `:LspInfo` to confirm that Neovim connected successfully. Diagnostics from the compiler will surface in the quickfix window, virtual text, or however you have LSP UI plugins configured.

## Troubleshooting

- Run `:checkhealth` to confirm Neovim can find the `sr_lang` binary.
- Make sure the version of `sr_lang` you built includes the `lsp` subcommand.
- Use `:lua vim.lsp.stop_client(vim.lsp.get_active_clients({ name = "sr-lang" }))` to restart the server after changing compiler code.
- Launch the server manually (`sr_lang lsp`) to observe raw JSON-RPC messages if you need to debug protocol issues.
