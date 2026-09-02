package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.CoverageConstruct;
import souther.compiler.types.CoverageOrigin;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A comprehension's guard is one fork, whichever of its two readers is asking.
 *
 * <p>The lowering turns a comprehension into the forks that run, and the reading that decides what a
 * coverage obligation is about happens before that, where a rule the caller supplied is still a
 * parameter. So the same guard is numbered twice, by two walks that see the comprehension at
 * different times and go along the guards in opposite directions. That an obligation names a fork
 * the tree has is exactly that the two answer alike.
 *
 * <p>What holds it is that the comprehension answers, and the readers ask. This says the lowering
 * builds what it answered, at each guard and not only at the first: a numbering off by a place, or
 * taken along the guards the way the lowering walks them, comes out here.
 */
class AGuardsForkIsTheOneTheLoweringBuildsTest {

    private static final SourcePos AT = new SourcePos(1, 1);

    @Test
    void eachGuardLowersToTheForkTheComprehensionAnswersFor() {
        Hir.ListComp comp = aComprehensionGuardedBy(3);

        List<CoverageOrigin> built = forksBuiltFor(comp);

        List<CoverageOrigin> answered = new ArrayList<>();
        for (int guard = 0; guard < comp.guards().size(); guard++) {
            answered.add(comp.forkOfGuard(guard));
        }
        assertEquals(answered, built,
                "the reading that runs before the lowering names these forks, and an obligation"
                        + " about one the lowering did not build is about nothing");
    }

    /** The control: the forks are told apart, so the pair above is a numbering and not one value
     *  answered over and over. */
    @Test
    void andTheForksOfOneComprehensionAreNotAllTheSame() {
        Hir.ListComp comp = aComprehensionGuardedBy(2);

        assertNotEquals(comp.forkOfGuard(0), comp.forkOfGuard(1),
                "two guards of one comprehension are two forks");
    }

    /**
     * A fork is one of the guards, and asking for one that is not refuses.
     *
     * <p>The fork before the first is what the construct itself is owed for, and a value answering
     * that from here would be an obligation about the comprehension wearing a guard's name. The
     * fork after the last is a branch the lowering does not build, and an obligation about one is
     * about nothing.
     */
    @Test
    void andWhatIsNotAGuardIsNotAFork() {
        Hir.ListComp comp = aComprehensionGuardedBy(2);

        assertThrows(IndexOutOfBoundsException.class, () -> comp.forkOfGuard(-1),
                "the fork before the first would pass for the comprehension's own obligation");
        assertThrows(IndexOutOfBoundsException.class, () -> comp.forkOfGuard(2),
                "the lowering builds a fork for each guard and no more");
    }

    /** The origins the lowering put on the {@code if} it built for each guard, outermost first —
     *  which is the first guard, an earlier guard standing over a later one. */
    private static List<CoverageOrigin> forksBuiltFor(Hir.ListComp comp) {
        List<CoverageOrigin> out = new ArrayList<>();
        Hir.Expr lowered = Lower.desugarExpr(comp);
        while (lowered instanceof Hir.If branch) {
            out.add(branch.origin());
            lowered = branch.then();
        }
        return out;
    }

    private static Hir.ListComp aComprehensionGuardedBy(int guards) {
        List<Hir.Expr> written = new ArrayList<>();
        for (int i = 0; i < guards; i++) {
            written.add(new Hir.BoolLit(true, AT, null));
        }
        return new Hir.ListComp(new Hir.IntLit(1, AT, null), written,
                CoverageOrigin.written("m", 0, CoverageConstruct.COMPREHENSION), AT, null);
    }
}
