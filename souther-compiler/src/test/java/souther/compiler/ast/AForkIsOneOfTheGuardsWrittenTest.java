package souther.compiler.ast;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A comprehension's fork is one of the guards it writes, and asking for another is refused.
 *
 * <p>What the fork of a guard is, is the comprehension's answer: two readers see it at different
 * times — the lowering that builds the forks, and the reading that decides who a fork's decision
 * belongs to — and neither works the numbering out for itself. That they agree is held where both
 * are run against each other; what is held here is that the answer is a fork at all.
 *
 * <p>The number before the first is what makes that worth saying. A fork is stored one past the
 * part it is of, so asking for the part before the first would answer with the comprehension's own
 * origin — the obligation the construct itself is owed for, handed back wearing a guard's name and
 * passing for one wherever forks are counted.
 */
class AForkIsOneOfTheGuardsWrittenTest {

    private static final SourcePos AT = new SourcePos(1, 1);

    @Test
    void whatIsNotAGuardIsNotAFork() {
        Hir.ListComp comp = aComprehensionGuardedBy(2);

        assertThrows(IndexOutOfBoundsException.class, () -> comp.forkOfGuard(-1),
                "the fork before the first would pass for the comprehension's own obligation");
        assertThrows(IndexOutOfBoundsException.class, () -> comp.forkOfGuard(2),
                "the lowering builds a fork for each guard and no more");
    }

    /** The control: the guards it does write have forks, and they are told apart. */
    @Test
    void andEachGuardWrittenHasAForkOfItsOwn() {
        Hir.ListComp comp = aComprehensionGuardedBy(2);

        assertNotEquals(comp.forkOfGuard(0), comp.forkOfGuard(1),
                "two guards of one comprehension are two forks");
        assertNotEquals(comp.origin(), comp.forkOfGuard(0),
                "a fork is not the obligation the comprehension itself is owed for");
    }

    private static Hir.ListComp aComprehensionGuardedBy(int guards) {
        List<Hir.Expr> written = new ArrayList<>();
        for (int i = 0; i < guards; i++) {
            written.add(new Hir.BoolLit(true, AT, null));
        }
        return new Hir.ListComp(new Hir.IntLit(1, AT, null), written,
                SourceConstructOrigin.written("m", 0, SourceConstruct.COMPREHENSION), AT, null);
    }
}
