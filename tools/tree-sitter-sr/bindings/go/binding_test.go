package tree_sitter_sr_test

import (
	"testing"

	tree_sitter "github.com/smacker/go-tree-sitter"
	"github.com/tree-sitter/tree-sitter-sr"
)

func TestCanLoadGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_sr.Language())
	if language == nil {
		t.Errorf("Error loading Sr grammar")
	}
}
