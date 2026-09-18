package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value for a dependency's answer is composed against every demand or against none of them.
 *
 * <p>The composer's half of what a region refusing a constraint means. A reading that meets a
 * condition its region cannot carry says so and goes on: the region it leaves still holds every row
 * that arrives, and what is written down is that the condition is unaccounted for. A composer has no
 * such move. Dropping the demand and composing anyway looks for a value in a region wider than what
 * was demanded, and whatever it finds is handed over as a value that answers the demand — so the
 * only sound answer is that nothing was composed.
 *
 * <p>Which is what a reader sees the difference in. The value composed without the demand took the
 * other rule of the same decision, and the page reported a rule no row takes — a gap a strict build
 * refuses over, standing for a model that states nothing of the kind. What is reported now is this
 * compiler being unable to answer for the dependency, which is where the shortfall is.
 */
class ADemandNoRegionCarriesIsNotComposedAgainstTest {

    /**
     * A decision turning on two positions of an answer that hold records.
     *
     * <p>Records, because a difference between two of them is read from end to end and stands on no
     * order — the one shape a region has to refuse. The demand reaches the composer as a form over
     * both positions, which is what makes this a test of the composer rather than of the reading.
     */
    private static final String RECORDS_COMPARED = """
            module example.demand

            data K = { id: Int }
            data R = { k: K, j: K }
            data Yes
            data No
            data Answer = Yes | No

            behavior look : (at: Int) -> R

            behavior decidesOnRecords : (at: Int) -> Answer
                depends on look
            let decidesOnRecords (at, look) = if look(at).k == look(at).j then Yes else No
            """;

    @Test
    void nothingIsComposedForADemandTheRegionCannotCarry() {
        String human = human(RECORDS_COMPARED);

        assertTrue(human.contains("nothing here could answer for a behavior a rule of the"
                        + " decision depends on"),
                () -> "the composer says it could not answer for the dependency: " + human);
        assertFalse(human.contains("no row takes a decision rule"),
                () -> "and no rule of the model is reported as one no row takes, which is what a"
                        + " value composed without the demand came to: " + human);
    }

    private static String human(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
