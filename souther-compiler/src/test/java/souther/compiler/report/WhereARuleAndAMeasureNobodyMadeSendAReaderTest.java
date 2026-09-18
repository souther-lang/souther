package souther.compiler.report;

import souther.compiler.meta.ModulePath;
import souther.compiler.publish.MeasureWord;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Where a rule nothing could read and a measure nobody made leave a reader, each held by a model
 * written to produce it.
 *
 * <p>Two of the arms {@link ReaderDisposition} answers with, and the models here are written for
 * them rather than found among the corpora. What a corpus reaches moves with the corpus: a model
 * made more adequate stops producing an entry, and an arm whose only reading came from one has
 * lost its witness without anyone deciding to take it away.
 *
 * <p><b>The input as well as the arm.</b> Reaching the arm says the switch answered; what it does
 * not say is that the entry it answered is the one this arm is for. So each of these pins the
 * uncertainty the analysis produced — its kind, its subject, and the reason it carries — beside
 * the disposition read off it.
 */
class WhereARuleAndAMeasureNobodyMadeSendAReaderTest {

    /**
     * A fork on a value worked out from the input, which nothing classifies.
     *
     * <p>Every class of the position is derived and both arms are reached; what stops is the
     * reading of the comparison inside, because it is about a value made from the position and
     * nothing works out what it says about the values there. That is a rule this compiler could not
     * read, and a rule is somewhere a reader can be sent.
     */
    private static final String A_RULE_NOTHING_READ = """
            module probe.ruleunread

            data Ordinary
            data Manager
            data Rank = Ordinary | Manager

            data Request = { rank: Rank }

            data Reasoned
            data Unreasoned

            let reasons (request: Request): List<Rank> =
                match request.rank with
                    | Ordinary -> [ Ordinary ]
                    | Manager  -> []

            behavior decide : (request: Request) -> Reasoned | Unreasoned
            let decide (request) =
                if List.isEmpty(reasons(request)) then Unreasoned else Reasoned

            example decide
                | "an ordinary rank has a reason" : (Request { rank = Ordinary }) -> Reasoned
                | "a manager has none" : (Request { rank = Manager }) -> Unreasoned
            """;

    /**
     * A behavior whose rules draw a line and which nobody has written a row for.
     *
     * <p>No row names it, so the measure of its signature was never made — and a measure that
     * could have found a gap and was not made is something a reader is owed a reason for. What
     * takes this away is writing a row, which is the mutation to make if the claim is in doubt.
     *
     * <p>The invariant keeps the model off the case beside this one. With no line the rules draw,
     * nothing is owed at all and the verdict is settled by having nothing to answer for, which is
     * a different thing from a measure nobody made.
     */
    private static final String A_MEASURE_NOBODY_MADE = """
            module probe.norows

            data Days = Int
                invariant value >= 1 && value <= 20

            data Grant = { days: Days }
            data NotEntitled

            behavior go : (worked: Int) -> Grant | NotEntitled
            """;

    private static AdequacyReport measured(String source) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation);
    }

    /** The one entry of this model whose disposition is the arm under test. */
    private static AdequacyUncertainty theOne(String source,
                                              Class<? extends ReaderDisposition> arm) {
        List<AdequacyUncertainty> found = measured(source).assessment().uncertainties().stream()
                .filter(each -> arm.isInstance(ReaderDisposition.of(each)))
                .toList();

        assertEquals(1, found.size(), () -> "this model is written to reach " + arm.getSimpleName()
                + " once, and what it reached was " + measured(source).assessment().uncertainties()
                        .stream().map(ReaderDisposition::of).toList());
        return found.getFirst();
    }

    /**
     * A rule this compiler could not read sends a reader to the rule.
     *
     * <p>The subject is the rule and not the behavior that holds it: a reader is sent to the thing
     * the reading stopped on, and a behavior has as many of these as its body has rules nothing
     * read.
     */
    @Test
    void aRuleNothingCouldReadSendsAReaderToTheRule() {
        AdequacyUncertainty it = theOne(A_RULE_NOTHING_READ, ReaderDisposition.LookAtTheRule.class);

        assertInstanceOf(AdequacyUncertainty.ByWeakening.class, it);
        assertInstanceOf(Subject.AtARule.class, it.subject());
        assertEquals(new ReaderDisposition.LookAtTheRule(it.subject()), ReaderDisposition.of(it));
    }

    /**
     * And a measure nobody made sends a reader to why nobody made it.
     *
     * <p>The reason travels and the word for it does not. What a person is shown is the sentence
     * that reason already has, and a document writing a second spelling of it would have two to
     * keep in step.
     */
    @Test
    void aMeasureNobodyMadeSendsAReaderToWhyNothingWasMeasured() {
        AdequacyUncertainty it =
                theOne(A_MEASURE_NOBODY_MADE, ReaderDisposition.LookAtWhyNothingWasMeasured.class);

        AdequacyUncertainty.NotMeasured never =
                assertInstanceOf(AdequacyUncertainty.NotMeasured.class, it);
        assertEquals(Adequacy.SignatureEvidence.NoRows.NO_ROWS, never.why());
        assertEquals(new Subject.OfAMeasure("probe.norows", "go", MeasureWord.SIGNATURE),
                never.subject());
        assertEquals(new ReaderDisposition.LookAtWhyNothingWasMeasured(it.subject(), never.why()),
                ReaderDisposition.of(it));
    }
}
