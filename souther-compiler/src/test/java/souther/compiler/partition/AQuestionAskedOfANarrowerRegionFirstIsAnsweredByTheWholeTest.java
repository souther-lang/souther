package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A question tried first with positions held apart, and then of the whole region it is about
 * ({@link NumericWitness#triedApartFirst}): an assignment either finds is the answer, a proof is
 * the whole region's alone, and where neither finds one both say what they fell short of.
 */
class AQuestionAskedOfANarrowerRegionFirstIsAnsweredByTheWholeTest {

    private static final CompositionShortfall FIRST = CompositionShortfall.of(
            Set.of(CompositionBudget.VALUES_THE_POSITIONS_ON_THE_WAY_ARE_TRIED_AT));

    private static final CompositionShortfall SECOND = CompositionShortfall.of(
            Set.of(CompositionBudget.PLACES_A_POSITION_ON_THE_WAY_IS_LOOKED_AT));

    private static final NumericTerm.FromOnePosition N = new NumericTerm.ValueOf(TermPath.of("n"));

    private static final Quantities QUANTITIES = quantities();

    private static final NumericWitness.Standing FOUND = assertInstanceOf(
            NumericWitness.Standing.Found.class, NumericWitness.of(QUANTITIES.region(), List.of(N),
                    term -> QUANTITIES.ordersOf(term).answered(),
                    NothingTheDeclarationsNarrow.LOOKING));

    private static final NumericWitness.Standing PROVED =
            new NumericWitness.Standing.ProvedImpossible();

    /**
     * Held apart from the one place the rules leave it, the position stands nowhere, which is no
     * answer about the question: the whole region places it there.
     */
    @Test
    void aPositionHeldApartFromTheOnePlaceItHasIsPlacedThereByTheWhole() {
        SearchRegion atFive = QUANTITIES.region().assuming(
                new LinearForm<>(ExactRatio.of(-5), Map.of(N, ExactRatio.ONE)), Rel.EQ).taken();

        NumericWitness.Standing standing = NumericWitness.triedApartFirst(atFive,
                List.of(new NumericWitness.HeldApart(N, Count.of(5))), List.of(N),
                term -> QUANTITIES.ordersOf(term).answered(), NothingTheDeclarationsNarrow.LOOKING,
                NumericWitness.Composing.ANY_ASSIGNMENT);

        NumericWitness.Standing.Found found =
                assertInstanceOf(NumericWitness.Standing.Found.class, standing);
        assertEquals(ExactRatio.of(5), Count.number(found.placeOf(N)).exactly());
    }

    @Test
    void anAssignmentTheNarrowerFoundIsTheAnswerAndTheWholeIsNotAsked() throws Exception {
        assertSame(FOUND, after(FOUND, () -> {
            throw new AssertionError("the whole is not asked once an assignment is found");
        }));
    }

    @Test
    void anAssignmentTheWholeFoundIsTheAnswer() throws Exception {
        assertSame(FOUND, after(PROVED, () -> FOUND));
        assertSame(FOUND, after(new NumericWitness.Standing.NotFound(FIRST), () -> FOUND));
    }

    /** What the narrower region falls short of is no reason a proof of the whole is not one. */
    @Test
    void aProofIsTheWholesAndSettlesTheNarrowerToo() throws Exception {
        assertSame(PROVED, after(PROVED, () -> PROVED));
        assertSame(PROVED, after(new NumericWitness.Standing.NotFound(FIRST), () -> PROVED));
    }

    /** And a proof of the narrower alone is none of the whole. */
    @Test
    void whereNeitherFoundOneBothShortfallsAreSaid() throws Exception {
        assertEquals(new NumericWitness.Standing.NotFound(FIRST.and(SECOND)),
                after(new NumericWitness.Standing.NotFound(FIRST),
                        () -> new NumericWitness.Standing.NotFound(SECOND)));
        assertEquals(new NumericWitness.Standing.NotFound(SECOND),
                after(PROVED, () -> new NumericWitness.Standing.NotFound(SECOND)));
    }

    /** The rule {@link NumericWitness#triedApartFirst} answers by, which nothing else reaches. */
    private static NumericWitness.Standing after(NumericWitness.Standing narrower,
                                                 Supplier<NumericWitness.Standing> whole)
            throws Exception {
        Method rule = NumericWitness.class.getDeclaredMethod("askedOfTheWholeAfter",
                NumericWitness.Standing.class, Supplier.class);
        rule.setAccessible(true);
        try {
            return (NumericWitness.Standing) rule.invoke(null, narrower, whole);
        } catch (InvocationTargetException thrown) {
            if (thrown.getCause() instanceof Error error) {
                throw error;
            }
            throw thrown;
        }
    }

    /** One whole number nothing narrows. */
    private static Quantities quantities() {
        Compilation compilation = ACompiledModel.answered("""
                module example.one

                data Ok = { v: Int }

                behavior f : (n: Int) -> Ok
                    constructs Ok

                let f (n) = Ok { v = 1 }
                """);
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get("f");
        assertNotNull(inputs, "the model under test compiles and reads its input");
        return inputs.quantities(rules);
    }
}
