package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.Prepared;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.Requirements;
import souther.compiler.numeric.Count;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What every element of a container has to meet is composed with no element where no element can
 * meet it.
 *
 * <p>An empty list meets every condition on its elements. So where the rules leave an element no
 * value the condition holds of, a row past it is a row holding none — and a composer that only
 * wrote elements meeting it would come back with nothing for a way an empty list takes.
 */
class WhatEveryElementMeetsIsComposedWithNoElementWhereNoneCanTest {

    /** `n > 0` is a value no `Item` holds. */
    private static final String MODEL = """
            module probe.vacuous

            data Item = { n: Int }
                invariant n >= -5 && n <= 0

            data Input = { items: List<Item>, gate: Int }
                invariant gate >= -10 && gate <= 10

            data A
            data B
            data C

            behavior decide : (x: Input) -> A | B | C
            let decide (x) =
                if List.length(x.items) > 2 then C
                else if List.all(i -> i.n > 0, x.items) then
                    if x.gate > 0 then A else B
                else C

            behavior allPositive : (x: Input) -> Bool
            let allPositive (x) = List.all(i -> i.n > 0, x.items)
            """;

    @Test
    void aRowPastItHoldsNoElementWhereNoElementCanMeetIt() {
        OnTheWay.TakenIn everyElement = everyElementPositive();
        assertInstanceOf(RowDemand.ForAll.class, everyElement.demand(),
                "every element meeting it, which a list holding none does");

        Axis gate = axisAt("x.gate");
        Generator.BoundaryAttempt attempt = Generator.probeFixing(subject(), "x.gate = 1",
                Map.of(new RealizationTarget.AtOnePosition(gate.term()), Count.of(1)),
                NumbersAskedFor.of(LevelRegion.point(new Level.OnACarrier(
                        domain("decide").quantities(rules()).ordersOf(gate.term()).answered(),
                        Count.of(1)))),
                new Reachability.Reaching(domain("decide").quantities(rules()).region(),
                        Requirements.NONE, List.of(everyElement)),
                Generator.CandidateCheck.ANY);

        assertEquals(List.of(), attempt.unrepresented().onTheWay(),
                "the condition was composed against: " + attempt.unrepresented());
        Generator.BoundaryAttempt.Built built = assertInstanceOf(
                Generator.BoundaryAttempt.Built.class, attempt, "a row past it: " + attempt);
        List<String> written = built.row().inputs().stream().map(FixtureTemplate::text).toList();
        assertTrue(written.stream().anyMatch(each -> each.contains("items = []")),
                () -> "and the row holds no element: " + written);
    }

    /** What `allPositive`'s body asks of a row coming out true, as the way past it. */
    private static OnTheWay.TakenIn everyElementPositive() {
        Bodies.Elaborated checked =
                COMPILATION.db().ask(new Bodies.Checked(module())).value();
        AnalysisBody analysis = checked.analysisBodies().get("allPositive");
        assertNotNull(analysis, "the model under test writes allPositive");
        InputDomain inputs = domain("allPositive");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                ElementBindings.of(analysis, rules().newtypes()));
        List<OnTheWay> stated = ReachingCuts.stating(Condition.of(analysis.core(), reads,
                        rules().symbols(), rules().newtypes(),
                        new ConditionNumbering(module(), "allPositive")),
                inputs.reading(rules()), true);
        assertEquals(1, stated.size(), () -> "one condition: " + stated);
        return assertInstanceOf(OnTheWay.TakenIn.class, stated.getFirst());
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

    private static Hir.SpecBehavior spec(String behavior) {
        Prepared prepared = COMPILATION.db().ask(new Shapes.Prepared(module())).value();
        return (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(each -> each.name().equals(behavior)).findFirst().orElseThrow();
    }

    private static InputDomain domain(String behavior) {
        InputDomain read = COMPILATION.db().ask(new Adequacy.Inputs(module())).value()
                .get(behavior);
        assertNotNull(read, "the model under test compiles");
        return read;
    }

    private static List<Axis> axes() {
        return COMPILATION.db().ask(new Adequacy.Divided(module(), "decide")).value().axes();
    }

    private static Axis axisAt(String path) {
        return axes().stream().filter(each -> each.path().toString().equals(path))
                .findFirst().orElseThrow(() -> new IllegalStateException(
                        "the model under test is measured at " + path + ", and this run has "
                                + axes().stream().map(each -> each.id().toString()).toList()));
    }

    private static MeasuredInput subject() {
        List<String> names = new ArrayList<>();
        spec("decide").params().forEach(each -> names.add(each.name()));
        assertTrue(names.contains("x"), "the model takes the input the row is fixed in");
        return MeasuredInput.of("decide", domain("decide").reading(rules()),
                AxesATestWrote.asAMeasurement("decide", axes()));
    }
}
