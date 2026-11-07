package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A question asked first of a narrower region, as a way to try it, and then of the whole region it
 * is about ({@link NumericWitness.Standing#orAskedOfTheWhole}): an assignment either finds is the
 * answer, a proof is the whole region's alone, and where neither finds one both say what they fell
 * short of.
 */
class AQuestionAskedOfANarrowerRegionFirstIsAnsweredByTheWholeTest {

    private static final CompositionShortfall FIRST = CompositionShortfall.of(
            Set.of(CompositionBudget.VALUES_THE_POSITIONS_ON_THE_WAY_ARE_TRIED_AT));

    private static final CompositionShortfall SECOND = CompositionShortfall.of(
            Set.of(CompositionBudget.PLACES_A_POSITION_ON_THE_WAY_IS_LOOKED_AT));

    private static final NumericWitness.Standing FOUND = found();

    private static final NumericWitness.Standing PROVED =
            new NumericWitness.Standing.ProvedImpossible();

    @Test
    void anAssignmentTheNarrowerFoundIsTheAnswerAndTheWholeIsNotAsked() {
        assertSame(FOUND, FOUND.orAskedOfTheWhole(() -> {
            throw new AssertionError("the whole is not asked once an assignment is found");
        }));
    }

    @Test
    void anAssignmentTheWholeFoundIsTheAnswer() {
        assertSame(FOUND, PROVED.orAskedOfTheWhole(() -> FOUND));
        assertSame(FOUND, new NumericWitness.Standing.NotFound(FIRST)
                .orAskedOfTheWhole(() -> FOUND));
    }

    /** What the narrower region falls short of is no reason a proof of the whole is not one. */
    @Test
    void aProofIsTheWholesAndSettlesTheNarrowerToo() {
        assertSame(PROVED, PROVED.orAskedOfTheWhole(() -> PROVED));
        assertSame(PROVED, new NumericWitness.Standing.NotFound(FIRST)
                .orAskedOfTheWhole(() -> PROVED));
    }

    /** And a proof of the narrower alone is none of the whole. */
    @Test
    void whereNeitherFoundOneBothShortfallsAreSaid() {
        assertEquals(new NumericWitness.Standing.NotFound(FIRST.and(SECOND)),
                new NumericWitness.Standing.NotFound(FIRST)
                        .orAskedOfTheWhole(() -> new NumericWitness.Standing.NotFound(SECOND)));
        assertEquals(new NumericWitness.Standing.NotFound(SECOND),
                PROVED.orAskedOfTheWhole(() -> new NumericWitness.Standing.NotFound(SECOND)));
    }

    /** One whole number nothing narrows, which any walk places somewhere. */
    private static NumericWitness.Standing found() {
        Compilation compilation = Compilation.ofSource("""
                module example.one

                data Ok = { v: Int }

                behavior f : (n: Int) -> Ok
                    constructs Ok

                let f (n) = Ok { v = 1 }
                """, "Main");
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get("f");
        assertNotNull(inputs, "the model under test compiles and reads its input");
        Quantities quantities = inputs.quantities(rules);
        NumericTerm n = new NumericTerm.ValueOf(TermPath.of("n"));
        return assertInstanceOf(NumericWitness.Standing.Found.class, NumericWitness.of(
                quantities.region(), List.of(n), term -> quantities.ordersOf(term).answered(),
                NothingTheDeclarationsNarrow.LOOKING));
    }
}
