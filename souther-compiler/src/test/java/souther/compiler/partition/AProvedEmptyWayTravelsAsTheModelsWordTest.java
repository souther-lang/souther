package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.Prepared;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Shapes;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A way whose conditions leave nothing standing reaches a reader as the model's word, and not as
 * something this compiler did not manage.
 *
 * <p>Two hops, and the second is the one a type change can quietly drop. The composer decides which
 * of the two kinds of news a condition carries; what a reader is told is decided a layer further on,
 * where every condition the row was not composed against is gathered into one list. A proof put into
 * that list by a composer that knows the difference and gathered by a layer that does not is a proof
 * a reader never sees.
 *
 * <p>What is not pinned here is the sentence. Whether it reads well is a wording question, and the
 * one thing a check could hold — that a word exists for this case at all — javac already holds,
 * because the answer is a sealed hierarchy every reader has to take apart.
 */
class AProvedEmptyWayTravelsAsTheModelsWordTest {

    private static final String BOUNDED = """
            module example.bounded

            data Amount = Int
                invariant value >= 0 && value <= 100
            data Req = { cost: Amount }
            data Res = { n: Int }

            behavior f : (r: Req) -> Res
            """;

    /**
     * A composer handed a way that leaves nothing says so, and says it of the condition it was
     * standing at.
     *
     * <p>Not as a value it could not compose. That word says a figure might be raised or a way of
     * building might be missing, and neither reaches a way the rules refuse — an author acting on it
     * would be looking for something to build where the model admits nothing.
     */
    @Test
    void theComposerSaysTheRulesLeftNothingRatherThanThatItComposedNothing() {
        Generator.BoundaryAttempt attempt = composing(NothingTheRulesLeave.REGION, CUT);

        assertEquals(1, attempt.unrepresented().size(),
                () -> "the one condition it was handed: " + attempt.unrepresented());
        ReachabilityGap said = attempt.unrepresented().get(0);
        assertInstanceOf(ReachabilityGap.ProvedImpossible.class, said,
                "the rules settled it, which is not the composer having fallen short");
        assertEquals(WHERE, said.anchor(),
                "and a reader is sent to where the proof was met, which is the condition's place");
    }

    /**
     * And no row comes of it, which is what the proof says.
     *
     * <p><b>The half a reader of the answer sees.</b> What the gap list holds is read by a report;
     * what everything else reads is which of the shapes the attempt is, and a row handed over with a
     * proof attached would be taken by every one of them as a row. The proof says the way leaves
     * nothing standing, so the row assembled on it does not arrive — and an answer built from it
     * travels on as a value of the dependency it was composed for.
     */
    @Test
    void noRowIsHandedOverForAWayTheRulesLeaveNothingOn() {
        Generator.BoundaryAttempt attempt = composing(NothingTheRulesLeave.REGION, CUT);

        assertEquals(Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE,
                assertInstanceOf(Generator.BoundaryAttempt.Unresolved.class, attempt,
                        "a way that leaves nothing standing is a way no row arrives by").why()
                        .reason(),
                "and the word is the model's, which is the one a reader may act on");
    }

    /**
     * A built row cannot be handed over carrying the proof at all.
     *
     * <p>Where the invariant is, rather than in each of the readers that rests on it. Every one of
     * them takes a built row as a row and reads the list beside it as what somebody could work on —
     * which was true of every entry that list could hold until this word was added to it, and would
     * have gone on being assumed by readers nothing told. Refused here, the assumption is a fact
     * about the type and the readers are right without having been changed.
     */
    @Test
    void aBuiltRowCannotCarryTheProof() {
        Generator.BoundaryAttempt built = composing(NothingTheRulesSay.REGION, CUT);
        Generator.GeneratedRow row = assertInstanceOf(Generator.BoundaryAttempt.Built.class, built,
                "a way that stands is a way a row is built on").row();

        assertThrows(IllegalArgumentException.class,
                () -> new Generator.BoundaryAttempt.Built(row,
                        List.of(new ReachabilityGap.ProvedImpossible(CUT))),
                "a row on a way that leaves nothing standing is a row that does not arrive");
    }

    /**
     * And a condition the composer could not place in a way that stands is still the composer's own
     * word.
     *
     * <p>The control. Both ways leave the account one entry, so a check counting entries would pass
     * either; what tells them apart is which of the two kinds of news the entry is. The condition
     * here is over a position the declarations put nothing at, which is a walk that found nothing —
     * and nothing about the model follows from it.
     */
    @Test
    void aConditionNothingCouldBePlacedUnderIsStillTheComposersOwnWord() {
        Generator.BoundaryAttempt attempt = composing(NothingTheRulesSay.REGION, ELSEWHERE);

        assertEquals(1, attempt.unrepresented().size(),
                () -> "the one condition it was handed: " + attempt.unrepresented());
        assertInstanceOf(ReachabilityGap.Uncomposed.class, attempt.unrepresented().get(0),
                "nothing was proved, so what is said is what this compiler did not manage");
    }

    /**
     * The layer that gathers what a row was not composed against carries the proof out with the
     * rest.
     *
     * <p>The hop the composer's answer has to survive. What a reader is handed is one list of
     * everything left out, built here out of the walk's own answers and the composer's — and the
     * proof is the only one of them a reader may act on, so a gather that kept the shapes it knew
     * and dropped this one would lose exactly the entry that was worth carrying.
     */
    @Test
    void theAccountCarriesTheProofOutWithWhatTheComposerCouldNotDo() {
        ReachabilityGap proof = new ReachabilityGap.ProvedImpossible(CUT);
        ItemAssessment.Attempt came = new ItemAssessment.Attempt.Unresolved(
                new Generator.UnresolvedCombination(List.of("r.cost = 100"),
                        Generator.UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED),
                WayToTheBorder.UNTOUCHED, List.of(proof));

        assertEquals(List.of(proof), came.unaccountedFor(),
                "the proof reaches a reader as itself");
    }

    /** Which question a report about the condition under test would put. */
    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("m",
                    new ConditionOccurrence("b", 0));

    private static final OnTheWay.TakenIn CUT = cutOver(
            new NumericTerm.ValueOf(souther.compiler.inputs.TermPath.of("r").then("cost")));

    /** A condition over a position the declarations put nothing at. */
    private static final OnTheWay.TakenIn ELSEWHERE = cutOver(
            new NumericTerm.ValueOf(souther.compiler.inputs.TermPath.of("r").then("elsewhere")));

    private static OnTheWay.TakenIn cutOver(NumericTerm over) {
        return new OnTheWay.TakenIn(WHERE,
                new TakenConstraint.Affine(LinearForm.atom(over), Rel.GE));
    }

    /** A row composed inside {@code within}, with {@code cut} on the way to it. */
    private static Generator.BoundaryAttempt composing(SearchRegion within, OnTheWay.TakenIn cut) {
        return Generator.probeFixing(subject(), "r.cost = 100",
                Map.of(new RealizationTarget.AtOnePosition(costAxis().term()), Count.of(100)),
                NumbersAskedFor.of(LevelRegion.point(
                        new Level.OnACarrier(Carrier.WHOLE, Count.of(100)))),
                new Reachability.Reaching(within, Requirements.NONE, List.of(cut)),
                Generator.CandidateCheck.ANY);
    }

    // The compilation, read once and answered from.
    private static final Compilation COMPILATION = compiled();

    private static Compilation compiled() {
        Compilation made = Compilation.ofSource(BOUNDED, "Main");
        made.answerEverything();
        return made;
    }

    private static String module() {
        return COMPILATION.modules().get(0);
    }

    private static RuleReadingSource rules() {
        return RuleReadings.of(COMPILATION, module());
    }

    private static Hir.SpecBehavior spec() {
        Prepared prepared = COMPILATION.db().ask(new Shapes.Prepared(module())).value();
        return (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(each -> each.name().equals("f")).findFirst().orElseThrow();
    }

    private static InputDomain domain() {
        InputDomain read = COMPILATION.db()
                .ask(new souther.compiler.query.Adequacy.Inputs(module())).value()
                .get(spec().name());
        assertNotNull(read, "the model under test compiles");
        return read;
    }

    private static Axis costAxis() {
        return Partitions.of(spec().name(), domain(), rules(), ReadAs.THE_COMPILATION_DOES)
                .axes().stream()
                .filter(each -> each.path().toString().equals("r.cost")).findFirst().orElseThrow();
    }

    private static MeasuredInput subject() {
        return MeasuredInput.of(spec().name(), domain().reading(rules()),
                Partitions.of(spec().name(), domain(), rules(), ReadAs.THE_COMPILATION_DOES));
    }
}
