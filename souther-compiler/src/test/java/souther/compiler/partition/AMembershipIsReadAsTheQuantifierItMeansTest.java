package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a container holds a value is read as the quantifier it means: holding it is some element
 * the value, and not holding it is every element another value.
 *
 * <p>The container is the position the argument stands at however it was written, so a helper
 * that answers a field of what it is handed is that field. A container built out of another is
 * not that other: an element of {@code Set.filter(p, xs)} is an element of {@code xs}, and the
 * other way round it is not, so what such a membership asks is nothing of {@code xs}.
 */
class AMembershipIsReadAsTheQuantifierItMeansTest {

    private static final String MODEL = """
            module probe.membership

            data Name = String
                invariant String.length(value) >= 1 && String.length(value) <= 8

            data Lead = { campaigns: Set<Name>, names: List<Name>, picked: Name }

            let campaignsOf (lead: Lead): Set<Name> = lead.campaigns

            behavior direct : (lead: Lead, priority: Name) -> Bool
            let direct (lead, priority) = Set.contains(priority, lead.campaigns)

            behavior helped : (lead: Lead, priority: Name) -> Bool
            let helped (lead, priority) = Set.contains(priority, campaignsOf(lead))

            behavior listed : (lead: Lead) -> Bool
            let listed (lead) = List.contains(lead.picked, lead.names)

            data LeadCommon = { campaigns: Set<Name> }
            data NewLead = { ...LeadCommon, fresh: Bool }
            data WorkingLead = { ...LeadCommon, touches: Int }
            data OpenLead = NewLead | WorkingLead

            let campaignsOfOpen (lead: OpenLead): Set<Name> = lead.campaigns

            behavior spread : (lead: OpenLead, priority: Name) -> Bool
            let spread (lead, priority) = Set.contains(priority, campaignsOfOpen(lead))

            behavior written : (lead: Lead) -> Bool
            let written (lead) = Set.contains(Name("q"), lead.campaigns)

            data Tally = { counts: List<Int> }

            behavior someBig : (t: Tally) -> Bool
            let someBig (t) = List.any(c -> c > 5, t.counts)

            behavior filtered : (lead: Lead, priority: Name) -> Bool
            let filtered (lead, priority) =
                Set.contains(priority, Set.filter(n -> n /= lead.picked, lead.campaigns))
            """;

    @Test
    void holdingTheValueIsSomeElementTheValue() {
        RowDemand.Exists some = assertInstanceOf(RowDemand.Exists.class, asked("direct", true));
        assertEquals("lead.campaigns", some.container().toString());
        assertEquals(List.of(new RowDemand.SameAs(TermPath.of("priority"))), some.ofAnElement());
    }

    @Test
    void notHoldingItIsEveryElementAnotherValue() {
        RowDemand.ForAll every = assertInstanceOf(RowDemand.ForAll.class, asked("direct", false));
        assertEquals("lead.campaigns", every.container().toString());
        assertEquals(List.of(new RowDemand.DifferentFrom(TermPath.of("priority"))),
                every.ofEachElement());
    }

    /** A helper answering a field of what it is handed is that field, both ways round. */
    @Test
    void aContainerAHelperAnswersIsThePositionItAnswers() {
        assertEquals(asked("direct", true), asked("helped", true));
        assertEquals(asked("direct", false), asked("helped", false));
    }

    /** And a list's, with the value at another position of the same parameter. */
    @Test
    void aListIsReadTheSameWay() {
        RowDemand.Exists some = assertInstanceOf(RowDemand.Exists.class, asked("listed", true));
        assertEquals("lead.names", some.container().toString());
        assertEquals(List.of(new RowDemand.SameAs(TermPath.of("lead").then("picked"))),
                some.ofAnElement());
    }

    /**
     * What a demand on a container's elements turns on is the container itself, and its size
     * where that is asked: a number of the container moved — how many it holds — may take away the
     * element that met it.
     *
     * <p>Held as the reader of a moved step reads it ({@code AnotherLineTheRowsAllow}): a moved
     * number turns a demand on where it stands at or under one of the demand's positions.
     */
    @Test
    void whatADemandOnTheElementsTurnsOnIsTheContainerItself() {
        for (String behavior : List.of("direct", "someBig")) {
            for (boolean holding : List.of(true, false)) {
                RowDemand.OfACondition asked = asked(behavior, holding);
                TermPath container = switch (asked) {
                    case RowDemand.Exists some -> some.container();
                    case RowDemand.ForAll every -> every.container();
                    case RowDemand.Relational _, RowDemand.ATruth _ -> throw new AssertionError(
                            "a demand on the elements: " + asked);
                };
                assertTrue(asked.positions().contains(container),
                        () -> "the container itself: " + asked.positions());
                Optional<RowDemand.Relational> size = switch (asked) {
                    case RowDemand.Exists some -> some.holdingOne();
                    case RowDemand.ForAll every -> every.holdingNone();
                    case RowDemand.Relational _, RowDemand.ATruth _ -> Optional.empty();
                };
                assertTrue(size.isPresent(), () -> "the size is a number here: " + asked);
                for (NumericTerm term : size.get().terms()) {
                    assertTrue(asked.positions().stream()
                                    .anyMatch(at -> term.subjectPath().isAtOrUnder(at)),
                            () -> "a move of " + term + " turns it on: " + asked.positions());
                }
            }
        }
    }

    /**
     * A container a name every case of a sum spreads is read as that name, and its size is a
     * number of the input there as well — read the way a size written in a comparison is.
     */
    @Test
    void aContainerEveryCaseSpreadsIsReadAtItsNameWithItsSize() {
        RowDemand.Exists some = assertInstanceOf(RowDemand.Exists.class, asked("spread", true));
        assertEquals("lead.campaigns", some.container().toString());
        assertTrue(some.holdingOne().isPresent(), () -> "the size is a number here: " + some);
    }

    /**
     * A value written in the source stands at no position, and the membership is declined as
     * that — read, and short of somewhere to read the value from — rather than as a shape this
     * has no words for.
     */
    @Test
    void aValueAtNoPositionIsDeclinedAsThat() {
        for (boolean holding : List.of(true, false)) {
            OnTheWay.Declined declined = assertInstanceOf(OnTheWay.Declined.class,
                    stated("written", holding));
            assertEquals(new OnTheWay.Why.TheMeaningWasNotRead(
                    new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.VALUE)), declined.why());
        }
    }

    /** A container built out of another asks nothing of the other. */
    @Test
    void aContainerBuiltOutOfAnotherIsNoPosition() {
        for (boolean holding : List.of(true, false)) {
            OnTheWay.Declined declined = assertInstanceOf(OnTheWay.Declined.class,
                    stated("filtered", holding));
            assertEquals(new OnTheWay.Why.TheMeaningWasNotRead(
                    new WhyUnread.AtNoPosition(WhyUnread.AtNoPosition.Place.CONTAINER)),
                    declined.why());
        }
    }

    private static RowDemand.OfACondition asked(String behavior, boolean holding) {
        return assertInstanceOf(OnTheWay.TakenIn.class, stated(behavior, holding)).demand();
    }

    /** What {@code behavior}'s body asks of a row coming out {@code holding}. */
    private static OnTheWay stated(String behavior, boolean holding) {
        Bodies.Elaborated checked =
                COMPILATION.db().ask(new Bodies.Checked(module())).value();
        assertNotNull(checked, () -> "the model under test compiles: "
                + COMPILATION.diagnostics().values().stream().flatMap(List::stream)
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                .toList());
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        assertNotNull(analysis, () -> "the model under test writes " + behavior);
        InputDomain inputs = COMPILATION.db().ask(new Adequacy.Inputs(module())).value()
                .get(behavior);
        assertNotNull(inputs, "the model under test compiles");
        InputReading reading = inputs.reading(rules());
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                reading.declared(), ElementBindings.of(analysis, rules().newtypes()),
                inputs.dependencies());
        List<OnTheWay> stated = ReachingCuts.stating(Condition.of(analysis.core(), reads,
                        rules().symbols(), rules().newtypes(),
                        new ConditionNumbering(module(), behavior)),
                reading, holding);
        assertEquals(1, stated.size(), () -> "one condition: " + stated);
        return stated.getFirst();
    }

    private static final Compilation COMPILATION = compiled();

    private static Compilation compiled() {
        Compilation made = Compilation.ofSource(MODEL, "Main");
        made.measure(Adequacy.Asked.fullReport());
        made.answerEverything();
        return made;
    }

    private static String module() {
        return COMPILATION.modules().getFirst();
    }

    private static RuleReadingSource rules() {
        return RuleReadings.of(COMPILATION, module());
    }
}
