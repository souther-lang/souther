package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

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

    /** A container built out of another asks nothing of the other. */
    @Test
    void aContainerBuiltOutOfAnotherIsNoPosition() {
        for (boolean holding : List.of(true, false)) {
            OnTheWay.Declined declined = assertInstanceOf(OnTheWay.Declined.class,
                    stated("filtered", holding));
            assertInstanceOf(OnTheWay.Why.ContainerAtNoPosition.class, declined.why());
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
                + COMPILATION.diagnostics());
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        assertNotNull(analysis, () -> "the model under test writes " + behavior);
        InputDomain inputs = COMPILATION.db().ask(new Adequacy.Inputs(module())).value()
                .get(behavior);
        assertNotNull(inputs, "the model under test compiles");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                ElementBindings.of(analysis, rules().newtypes()));
        List<OnTheWay> stated = ReachingCuts.stating(Condition.of(analysis.core(), reads,
                        rules().symbols(), rules().newtypes(),
                        new ConditionNumbering(module(), behavior)),
                inputs.reading(rules()), holding);
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
