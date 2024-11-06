package tree_sitter_raven_test

import (
	"testing"

	tree_sitter "github.com/smacker/go-tree-sitter"
	"github.com/tree-sitter/tree-sitter-raven"
)

func TestCanLoadGrammar(t *testing.T) {
	language := tree_sitter.NewLanguage(tree_sitter_raven.Language())
	if language == nil {
		t.Errorf("Error loading Raven grammar")
	}
}
