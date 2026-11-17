package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An {@code if} with one branch written as a truth is read as the connective that says the same,
 * so a clause written either way is one shape.
 *
 * <p>Held on the four ways a branch is written and on the clause denied, since the polarity of each
 * half is what a reader below takes its meaning from: {@code if c then p else false} stated is both
 * of {@code c} and {@code p} stated, and denied is a choice between each denied.
 */
class AnIfWithAWrittenBranchIsTheConnectiveItSaysTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "f");

    @Test
    void aWrittenBranchSaysWhatTheConnectiveItIsEquivalentToSays() {
        Core c = rule(0, 1);
        Core p = rule(1, 2);
        Map<String, String> said = new LinkedHashMap<>();
        said.put("if c then p else false", describe(ClauseExpr.of(branching(c, p, false), true)));
        said.put("if c then false else p", describe(ClauseExpr.of(branching(c, false, p), true)));
        said.put("if c then true else p", describe(ClauseExpr.of(branching(c, true, p), true)));
        said.put("if c then p else true", describe(ClauseExpr.of(branching(c, p, true), true)));
        said.put("not (if c then p else false)",
                describe(ClauseExpr.of(branching(c, p, false), false)));

        Map<String, String> expected = new LinkedHashMap<>();
        expected.put("if c then p else false", "BOTH c p");
        expected.put("if c then false else p", "BOTH !c p");
        expected.put("if c then true else p", "EITHER c p");
        expected.put("if c then p else true", "EITHER !c p");
        expected.put("not (if c then p else false)", "EITHER !c !p");
        assertEquals(expected, said);
    }

    /** What a shape composes and how each half stands, as {@code BOTH c p} or {@code EITHER !c p}. */
    private static String describe(ClauseExpr shape) {
        ClauseExpr.Joined joined = (ClauseExpr.Joined) shape;
        ConditionJoin how = joined.how();
        return how + " " + stood(joined.left(), "c") + " " + stood(joined.right(), "p");
    }

    private static String stood(ClauseExpr half, String name) {
        return (((ClauseExpr.Leaf) half).positive() ? "" : "!") + name;
    }

    private static Core rule(int ordinal, int least) {
        return new Core.Binary(BinOp.GE,
                new Core.Read("v" + ordinal, new BindingId(OWNER, ordinal), Type.INT, POS),
                new Core.Int(least, Type.INT, POS), Core.BinaryReading.AS_THEY_STAND,
                ConstructOccurrence.unwritten(), Type.BOOL, POS);
    }

    private static Core written(boolean truth) {
        return new Core.Bool(truth, Type.BOOL, POS);
    }

    private static Core branching(Core condition, Object then, Object otherwise) {
        return new Core.If(condition, branch(then), branch(otherwise),
                Core.ForkPlace.asWritten(ConstructOccurrence.unwritten()), Type.BOOL, POS);
    }

    private static Core branch(Object branch) {
        return branch instanceof Boolean truth ? written(truth) : (Core) branch;
    }
}
