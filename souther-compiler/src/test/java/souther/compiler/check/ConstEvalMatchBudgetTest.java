package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.SourcePos;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Folding {@code String.matches} answers where answering is cheap and declines where it is not. A
 * backtracking engine recurses over its subject, and the walk that asks this fails open on a
 * {@code RuntimeException} — which a {@code StackOverflowError} is not — so an unbounded attempt
 * would end the compilation rather than the fold.
 */
class ConstEvalMatchBudgetTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static Optional<Object> fold(String pattern, String subject) {
        return ConstEval.eval(new Ast.Apply("String.matches",
                List.of(new Ast.StringLit(pattern, POS, null), new Ast.StringLit(subject, POS, null)), POS, null));
    }

    @Test
    void aPatternOverAWrittenSubjectFolds() {
        assertEquals(Optional.of(true), fold("[0-9][A-E]", "1A"));
        assertEquals(Optional.of(false), fold("[0-9][A-E]", "zz"));
    }

    @Test
    void aSubjectPastTheBudgetIsLeftToTheRunTime() {
        // Far past what the budget allows the engine to read, and far past what it can recurse over
        assertTrue(fold("(a|b)*", "a".repeat(100_000)).isEmpty(),
                "declined rather than answered, and the compilation goes on");
    }
}
