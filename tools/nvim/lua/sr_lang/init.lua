local M = {}

local function default_root_dir(fname, markers)
  if not fname or fname == "" then
    return vim.loop.cwd()
  end
  local path = vim.fs.dirname(fname)
  if not path or path == "" then
    return vim.loop.cwd()
  end
  local root = vim.fs.find(markers, { path = path, upward = true })[1]
  if root then
    local parent = vim.fs.dirname(root)
    if parent and parent ~= "" then
      return parent
    end
  end
  return path
end

function M.setup(opts)
  opts = opts or {}
  local cmd = opts.cmd or { "sr_lang", "lsp" }
  local filetypes = opts.filetypes or { "sr" }
  local root_markers = opts.root_markers or { "sr-project.toml", "sr-project.json", "srconfig.toml", ".git" }
  local group = vim.api.nvim_create_augroup("SrLangLsp", { clear = true })

  vim.api.nvim_create_autocmd("FileType", {
    group = group,
    pattern = filetypes,
    callback = function(args)
      local bufnr = args.buf
      local name = opts.name or "sr-lang"
      local capabilities = opts.capabilities or vim.lsp.protocol.make_client_capabilities()
      local on_attach = opts.on_attach
      local settings = opts.settings
      local root_dir

      if type(opts.root_dir) == "function" then
        root_dir = opts.root_dir(vim.api.nvim_buf_get_name(bufnr))
      else
        root_dir = opts.root_dir
      end
      if not root_dir or root_dir == "" then
        root_dir = default_root_dir(vim.api.nvim_buf_get_name(bufnr), root_markers)
      end

      local existing = vim.lsp.get_active_clients({ bufnr = bufnr, name = name })
      if next(existing) then
        return
      end

      vim.lsp.start({
        name = name,
        cmd = cmd,
        root_dir = root_dir,
        filetypes = filetypes,
        capabilities = capabilities,
        on_attach = on_attach,
        settings = settings,
        single_file_support = opts.single_file_support ~= false,
        workspace_folders = opts.workspace_folders,
        init_options = opts.init_options,
        cmd_env = opts.cmd_env,
        handlers = opts.handlers,
        flags = opts.flags,
        before_init = opts.before_init,
        on_init = opts.on_init,
        on_exit = opts.on_exit,
        trace = opts.trace,
      })
    end,
  })
end

return M
