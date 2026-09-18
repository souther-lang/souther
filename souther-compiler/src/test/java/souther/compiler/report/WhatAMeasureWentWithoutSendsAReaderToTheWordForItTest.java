package souther.compiler.report;

import souther.compiler.publish.WeakeningVocabulary;
import souther.compiler.publish.WeakeningWord;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Weakening;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a measure that went without something leaves a reader, held by a model written to go
 * without it.
 *
 * <p>{@link ReaderDisposition.LookAtWhatTheMeasureWentWithout} is the arm for everything a weakening
 * names that is neither a rule nor a fork nor an arm. There is no rule to send a reader to at any
 * of them, so what they are sent to is the word this document has for what the measure went
 * without — and an arm nothing reaches is an arm nobody has seen answer.
 *
 * <p><b>Its own model and not a reading of the corpus.</b> The models this repository carries are
 * evidence about the language, and one of them reaches this arm only while it is short of
 * something: made more adequate, it stops, and the arm loses its only witness without anyone
 * meaning to take it away. So the witness is written here, to be short on purpose.
 *
 * <p><b>Through the analysis and not by building the value.</b> A disposition worked out from a
 * hand-made entry says the switch over the arms is total, which javac already says. What has to
 * hold is that a model produces an entry this arm answers, which is a claim about the walk.
 */
class WhatAMeasureWentWithoutSendsAReaderToTheWordForItTest {

    /**
     * A body the rules refuse, so nothing lowers it.
     *
     * <p>The construction is the one the invariant rejects, and a behavior whose body was never
     * elaborated is short of what its rows took. That shortfall is about the module and not about
     * any rule of it: there is no rule to go back to, which is the case this arm exists for.
     */
    private static final String MODEL = """
            module probe.unelaborated

            data Seat = Int
                invariant value >= 1 && value <= 300

            behavior hold : (party: Int) -> Seat
                constructs Seat

            let hold (party) = Seat(0)
            """;

    /**
     * A second module, whose rows reach one of its behavior's two outputs.
     *
     * <p>A measure that was made and found an output nothing witnesses, which is a gap and refuses
     * the verdict over the compilation the two are in. Its own module and not another behavior
     * beside the first: a body nothing elaborated leaves its module's other measures unable to find
     * a gap, so a second behavior written here would produce no refusal to stand beside.
     */
    private static final String A_MODULE_WITH_A_GAP = """
            module probe.uncovered

            data Small
            data Large
            data Size = Small | Large

            data Refunded
            data Kept

            behavior settle : (size: Size) -> Refunded | Kept
            let settle (size) =
                match size with
                    | Small -> Refunded
                    | Large -> Kept

            example settle
                | "a large one is kept" : (Large) -> Kept
            """;

    private static AdequacyReport measured() {
        return measured(List.of(MODEL));
    }

    private static AdequacyReport measured(List<String> sources) {
        Compilation compilation = Compilation.ofSources(sources, ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation);
    }

    /**
     * The model goes without something, and where that leaves a reader is the word for it.
     *
     * <p>Read off the assessment. What this model's verdict is depends on what else it is short of
     * and is not what this is about — an entry is answered by the same arm whether or not something
     * outranks it ({@link AdequacyReport#assessment()}).
     */
    @Test
    void aModuleWhoseBodiesWereNotMadeSendsAReaderToWhatTheMeasureWentWithout() {
        List<ReaderDisposition> reached = measured().assessment().uncertainties().stream()
                .map(ReaderDisposition::of)
                .filter(ReaderDisposition.LookAtWhatTheMeasureWentWithout.class::isInstance)
                .toList();

        assertEquals(1, reached.size(),
                () -> "this model is written to go without one thing that is not a rule, a fork or"
                        + " an arm, and what it reached was " + measured().assessment()
                                .uncertainties().stream().map(ReaderDisposition::of).toList());
        ReaderDisposition.LookAtWhatTheMeasureWentWithout it = assertInstanceOf(
                ReaderDisposition.LookAtWhatTheMeasureWentWithout.class, reached.getFirst());
        assertEquals(new Subject.OfAModule("probe.unelaborated"), it.subject());
        assertEquals(new WeakeningVocabulary.AWordOfThisDocuments(
                WeakeningWord.BODIES_NOT_ELABORATED), it.said());
    }

    /**
     * And it arrives through the walk rather than from a value this test built.
     *
     * <p>What makes the assertion above a claim about the analysis is that the entry it answers was
     * produced by measuring a model. Written the other way — an entry constructed here and handed
     * to the switch — it would hold over a value no model produces.
     */
    @Test
    void theEntryAnsweredIsOneTheAnalysisProduced() {
        List<AdequacyUncertainty> unresolved = measured().assessment().uncertainties();

        assertTrue(unresolved.stream().anyMatch(each ->
                        each instanceof AdequacyUncertainty.ByWeakening it
                                && it.cause() instanceof Weakening.BodiesNotElaborated),
                () -> "nothing here says a body was never elaborated: " + unresolved);
    }

    /**
     * And a gap somewhere else in the model does not take the witness away.
     *
     * <p>Which is what makes this a witness rather than a reading of one verdict. A gap refuses the
     * verdict and the report then shows a reader nothing that holds it open — the module is short
     * of the same thing either way, and the arm answering it is the same arm.
     */
    @Test
    void aGapElsewhereRefusesTheVerdictAndLeavesTheWitnessStanding() {
        AdequacyReport refused = measured(List.of(MODEL, A_MODULE_WITH_A_GAP));

        assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED, refused.adequacy(),
                () -> "the second behavior is here to be a gap and is not one: "
                        + refused.adequacyGaps());
        assertTrue(refused.whatKeepsTheVerdictOpen().isEmpty(),
                "a refused verdict is open on nothing");
        assertTrue(refused.assessment().uncertainties().stream()
                        .map(ReaderDisposition::of)
                        .anyMatch(ReaderDisposition.LookAtWhatTheMeasureWentWithout.class
                                ::isInstance),
                () -> "the gap took the witness with it: " + refused.assessment().uncertainties());
    }
}
