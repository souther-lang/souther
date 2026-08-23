package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.AdequacyPolicy;
import souther.compiler.partition.Budgets;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a measurement may spend is the compilation's to set, and what spending it costs is reported.
 *
 * <p>Two things and the second is why the first matters. That the number can be set is rule 4; that
 * a measurement held to a small one says what it was short of is rule 3. Tested together because a
 * budget that can be lowered and reports nothing is the arrangement issue #969 removed, under a new
 * name.
 *
 * <p>Held against a small budget rather than a large model. Every default is set with room over
 * anything in this repository, so the only way to reach the path past one is to say what the budget
 * is — which is what having it as an input is for, and what a private constant made impossible.
 */
class ABudgetIsTheCompilationsToSetTest {

    /** Two positions of two classes each, which is four pairs — one more than a budget of three. */
    private static final String FOUR_PAIRS = """
            module example.pairs

            data A
            data B
            data Flag = A | B
            data Res = { n: Int }

            behavior pick : (x: Flag, y: Flag) -> Res
                constructs Res
            let pick (x, y) = Res { n = 1 }

            example pick
                | "one" : (A, A) -> Res { n = 1 }
            """;

    /**
     * A pair space past the budget leaves the measure partial and says which limit did it.
     *
     * <p>The same model twice, and only the budget differs — so the two answers are the budget's
     * and not the model's. Read with one compilation, a partial measurement is as good an account
     * of a model this cannot read at all.
     */
    @Test
    void aPairSpacePastTheBudgetIsReportedAsPartial() {
        PartitionEvidence wide = evidenceFor(FOUR_PAIRS, Budgets.measures().pairSpace());
        PartitionEvidence narrow = evidenceFor(FOUR_PAIRS, 3);

        assertInstanceOf(Measurement.Complete.class, wide.pairs().counted(),
                () -> "at the standard budget the space is walked: " + wide.pairs());
        assertInstanceOf(Measurement.Partial.class, narrow.pairs().counted(),
                () -> "and past a budget of three it is not: " + narrow.pairs());
        assertEquals(4, narrow.pairs().total(),
                "the size of the space is what the model says, whatever was walked of it");
    }

    /**
     * A budget that admits nothing is refused where it is written.
     *
     * <p>Each of the three, because each is a different sentence about a different walk. A bound of
     * nought is not a small bound: it measures nothing and reports every model as partial over a
     * space it never entered, which is a compilation saying less about every model than one with no
     * bound at all would.
     */
    @Test
    void aBudgetBelowOneIsRefused() {
        assertThrows(IllegalArgumentException.class,
                () -> new AdequacyPolicy.OfTheMeasures(0), "a pair space of nought");
        assertThrows(IllegalArgumentException.class,
                () -> new AdequacyPolicy.OfTheGeneration(0, 4096), "no rows");
        assertThrows(IllegalArgumentException.class,
                () -> new AdequacyPolicy.OfTheGeneration(200, 0), "no cells");
    }

    /** And the standard one is a policy, so the three numbers are read from one place. */
    @Test
    void theStandardBudgetIsWhatACompilationSets() {
        assertTrue(Budgets.measures().pairSpace() > 0);
        assertTrue(Budgets.generation().rows() > 0);
        assertTrue(Budgets.generation().cellsPerGroup() > 0);
    }

    private static PartitionEvidence evidenceFor(String source, int pairSpace) {
        Compilation compilation = Compilation.ofSource(source, "Main")
                .withAdequacyPolicy(new AdequacyPolicy(
                        new AdequacyPolicy.OfTheMeasures(pairSpace), Budgets.generation()));
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> partitions = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        PartitionEvidence evidence = partitions.get("pick");
        assertNotNull(evidence, "the behavior was measured");
        return evidence;
    }
}
