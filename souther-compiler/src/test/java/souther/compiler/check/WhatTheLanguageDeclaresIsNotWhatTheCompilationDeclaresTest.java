package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeName;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A declaration the language gives resolves and types like any other, and is declared by no module
 * of the compilation.
 *
 * <p>{@link Declarations} answers both questions and keeps them apart: {@code declaration} sees the
 * language's vocabulary beside the compilation's, because a name that denotes one types like a name
 * that denotes the other, and {@code declaredByCompilation} does not, because what a compilation may
 * construct is governed by {@code constructs} and the language's vocabulary is not.
 *
 * <p>Held here because the two sources are separately readable and could be folded into one — the
 * registry could answer for the prelude and every reader would go on compiling. What would go is the
 * distinction, silently: {@code RoundingMode} would become something this compilation declares.
 */
class WhatTheLanguageDeclaresIsNotWhatTheCompilationDeclaresTest {

    private static final String APP = """
            module app

            data Note = { text: String }
            """;

    /** The language's own data is there to be read. */
    @Test
    void aRuntimeBackedDeclarationIsAnswered() {
        assertNotNull(declarations().declaration(TypeName.runtime("RoundingMode").key()));
        assertTrue(declarations().contains(TypeName.runtime("RoundingMode").key()));
    }

    /** And is declared by no module here. */
    @Test
    void andIsNotDeclaredByThisCompilation() {
        assertFalse(declarations().declaredByCompilation(TypeName.runtime("RoundingMode").key()));
    }

    /** While what the compilation writes answers yes to both. */
    @Test
    void aDeclarationOfThisCompilationAnswersBoth() {
        TypeName note = TypeSymbols.declared(new TypeKey("app", "Note"));

        assertNotNull(declarations().declaration(note.key()));
        assertTrue(declarations().declaredByCompilation(note.key()));
    }

    /** And a name neither of them declares is answered by neither. */
    @Test
    void aNameNothingDeclaresIsAnsweredByNeither() {
        TypeName nothing = TypeSymbols.declared(new TypeKey("app", "Missing"));

        assertNull(declarations().declaration(nothing.key()));
        assertFalse(declarations().declaredByCompilation(nothing.key()));
    }

    private static Declarations declarations() {
        Ast.Module parsed = CstFrontend.parse(APP);
        return Symbols.of(Resolve.module(parsed, SyntaxSymbols.of(parsed))).declarations();
    }
}
