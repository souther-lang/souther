package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.ApplicationOrigin;
import souther.compiler.types.ReachName;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.SourceReferenceOrigin;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Folding {@code String.matches} answers where answering is cheap and declines where it is not.
 *
 * <p>The fold walks the machine the pattern means, so a long subject is a long walk and nothing
 * else: each symbol is read once, and no subject is past what the fold answers. What may cost more
 * than the fold will spend is building the machine, and a pattern whose machine is past the
 * allowance leaves the match to the run time.
 */
class ConstEvalMatchBudgetTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static Optional<Object> fold(String pattern, String subject) {
        ValueName.Stdlib.Operation matches = ValueName.Stdlib.operation("String", "matches");
        // Folded against the real library, because which operation folds is asked as the kernel
        // that library declares it to be. No module of its own: the call names a library operation
        // and nothing else.
        return ConstEval.against(Symbols.none(DefaultStdlib.get())).eval(Hir.Apply.synthetic("String.matches",
                new ReachName.OfLibrary(matches),
                new SourceReferenceOrigin(new WrittenOwner.Body("m", "b"), 0),
                new ApplicationOrigin.Written(SourceConstructOrigin.written(
                        new WrittenOwner.Body("m", "b"), 0, SourceConstruct.CALL)),
                List.of(new Hir.StringLit(pattern, POS, null), new Hir.StringLit(subject, POS, null)),
                POS, null));
    }

    @Test
    void aPatternOverAWrittenSubjectFolds() {
        assertEquals(Optional.of(true), fold("[0-9][A-E]", "1A"));
        assertEquals(Optional.of(false), fold("[0-9][A-E]", "zz"));
    }

    /** A subject a backtracking engine would recurse too deeply over is a walk like any other. */
    @Test
    void aLongSubjectIsAnswered() {
        assertEquals(Optional.of(true), fold("(a|b)*", "a".repeat(100_000)));
        assertEquals(Optional.of(false), fold("(a|a)*b", "a".repeat(100_000)));
    }

    /** A machine past what the fold may build is left to the run time. */
    @Test
    void aPatternPastTheAllowanceIsLeftToTheRunTime() {
        assertTrue(fold("a{60000}", "a").isEmpty(),
                "declined rather than answered, and the compilation goes on");
    }

    /** Text that is no pattern is refused where the call is checked; the fold has nothing to answer
     *  with. */
    @Test
    void textThatIsNoPatternIsNotFolded() {
        assertTrue(fold("(a)\\1", "aa").isEmpty());
    }
}
