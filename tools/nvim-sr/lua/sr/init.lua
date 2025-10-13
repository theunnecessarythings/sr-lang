local M = {}

local function default_grammar_path()
  local source = debug.getinfo(1, 'S').source:sub(2)
  local plugin_dir = vim.fn.fnamemodify(source, ':p:h:h')
  local repo_root = vim.fn.fnamemodify(plugin_dir, ':p:h')
  return repo_root .. '/tree-sitter-sr'
end

function M.setup(opts)
  opts = opts or {}
  local grammar_path = opts.grammar_path or default_grammar_path()

  local parsers = require('nvim-treesitter.parsers').get_parser_configs()
  parsers.sr = parsers.sr or {}
  parsers.sr.install_info = {
    url = grammar_path,
    files = {'src/parser.c'},
    generate = true,
    requires_generate_from_grammar = true,
  }
  parsers.sr.filetype = 'sr'
  parsers.sr.maintainers = { 'sr-lang contributors' }

  vim.api.nvim_create_autocmd({ 'BufNewFile', 'BufRead' }, {
    pattern = { '*.sr' },
    callback = function()
      vim.bo.filetype = 'sr'
    end,
  })

  if vim.treesitter and vim.treesitter.language and vim.treesitter.language.register then
    vim.treesitter.language.register('sr', 'sr')
  end
end

return M
