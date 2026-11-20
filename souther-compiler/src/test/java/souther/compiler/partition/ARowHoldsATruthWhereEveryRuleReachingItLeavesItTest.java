package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Some row holds a truth at a place, whatever every other place holds, where every rule reaching
 * the place was read and leaves the truth a value, its own type's among them, no rule ties the
 * place to another, and no container holds it. Each case takes one of those away.
 */
class ARowHoldsATruthWhereEveryRuleReachingItLeavesItTest {

    private static final InputReading READ = reading();

    /** {@code o} is a truth its own type holds to true; {@code q.only} the same inside a record,
     *  which the reading of the record does not read; {@code e.x} one a rule ties to {@code e.y}. */
    private static InputReading reading() {
        Compilation compilation = ACompiledModel.answered("""
                module m

                data OnlyTrue = Bool
                    invariant value == true

                data Q = { free: Bool, only: OnlyTrue }

                data E = { x: Bool, y: Bool }
                    invariant x || y

                data Yes

                behavior f : (o: OnlyTrue, q: Q, e: E, flags: List<Bool>) -> Yes
                let f (o, q, e, flags) = Yes
                """);
        String module = compilation.modules().getFirst();
        return compilation.db().ask(new Adequacy.Inputs(module)).value().get("f")
                .reading(RuleReadings.of(compilation, module));
    }

    private static boolean held(TermPath at, boolean truth) {
        return UndividedByARelation.aRowHoldsTheTruth(new RowDemand.ATruth(at, truth), READ);
    }

    @Test
    void eitherTruthOfAPlaceNoRuleReadsIsHeld() {
        TermPath free = TermPath.of("q").then("free");

        assertTrue(held(free, true));
        assertTrue(held(free, false));
    }

    @Test
    void aTruthItsOwnTypeRefusesIsNotHeld() {
        assertTrue(held(TermPath.of("o"), true));
        assertFalse(held(TermPath.of("o"), false));
    }

    /** No rule of {@code Q} reads {@code only}, but its own type's rule is not read there. */
    @Test
    void aTruthOfAPlaceARuleWasNotReadAtIsNotHeld() {
        assertFalse(held(TermPath.of("q").then("only"), false));
    }

    /** Every rule was read and leaves {@code x} either truth, but only beside some {@code y}. */
    @Test
    void aTruthOfAPlaceARuleTiesToAnotherIsNotHeld() {
        assertFalse(held(TermPath.of("e").then("x"), false));
    }

    @Test
    void aTruthOfAnElementIsNotHeld() {
        assertFalse(held(TermPath.of("flags").element(), true));
    }
}
