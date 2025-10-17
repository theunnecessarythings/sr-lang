local M = {}

local function normalize(path)
  if vim.fs and vim.fs.normalize then
    return vim.fs.normalize(path)
  end

  return vim.fn.fnamemodify(path, ':p')
end

local function dir_exists(path)
  local stat = vim.loop.fs_stat(path)
  return stat and stat.type == 'directory'
end

local function default_grammar_path()
  local source = debug.getinfo(1, 'S').source:sub(2)
  local module_dir = vim.fn.fnamemodify(source, ':p:h')
  local plugin_root = vim.fn.fnamemodify(module_dir, ':p:h')
  local tools_dir = vim.fn.fnamemodify(plugin_root, ':p:h')

  local bundled = normalize(tools_dir .. '/tree-sitter-sr')
  if dir_exists(bundled) then
    return bundled
  end

  local legacy = normalize(plugin_root .. '/tree-sitter-sr')
  if dir_exists(legacy) then
    return legacy
  end

  return 'https://github.com/sr-lang/tree-sitter-sr'
end

local function set_filetype_detection()
  if vim.filetype and vim.filetype.add then
    vim.filetype.add({ extension = { sr = 'sr' } })
    return
  end

  local group = vim.api.nvim_create_augroup('sr-filetype', { clear = true })
  vim.api.nvim_create_autocmd({ 'BufNewFile', 'BufRead' }, {
    group = group,
    pattern = { '*.sr' },
    callback = function()
      vim.bo.filetype = 'sr'
    end,
  })
end

local function configure_parser(grammar_path)
  local has_parsers, parsers = pcall(require, 'nvim-treesitter.parsers')
  if not has_parsers then
    vim.notify(
      '[sr] nvim-treesitter not found. Install nvim-treesitter to enable sr syntax highlighting.',
      vim.log.levels.WARN
    )
    return
  end

  local configs = parsers.get_parser_configs()
  configs.sr = configs.sr or {}
  local is_remote = grammar_path:match('^https?://') or grammar_path:match('^git@')
  if not is_remote and not dir_exists(grammar_path) then
    vim.notify(
      string.format('[sr] Tree-sitter grammar not found at %s', grammar_path),
      vim.log.levels.ERROR
    )
    return
  end
  configs.sr.install_info = vim.tbl_deep_extend('force', configs.sr.install_info or {}, {
    url = grammar_path,
    files = { 'src/parser.c', 'src/scanner.c' },
    generate = true,
    requires_generate_from_grammar = true,
  })
  configs.sr.filetype = 'sr'
  configs.sr.maintainers = configs.sr.maintainers or { 'sr-lang contributors' }
  configs.sr.used_by = configs.sr.used_by or { 'sr' }
end

function M.setup(opts)
  opts = opts or {}
  local grammar_path = opts.grammar_path or default_grammar_path()
  if grammar_path and not grammar_path:match('^https?://') and not grammar_path:match('^git@') then
    grammar_path = normalize(grammar_path)
  end

  configure_parser(grammar_path)
  set_filetype_detection()

  if vim.treesitter and vim.treesitter.language and vim.treesitter.language.register then
    vim.treesitter.language.register('sr', 'sr')
  end
end

return M
