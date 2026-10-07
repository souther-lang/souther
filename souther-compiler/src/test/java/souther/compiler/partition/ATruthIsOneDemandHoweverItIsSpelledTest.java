package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A {@code Bool} position read as a truth asks a row for one of its two values, whichever way the
 * condition was written.
 *
 * <p>The bare read, the comparison against a written truth either way round, and the denial of
 * either all ask the same thing of a row, so each is one demand: the value at the position. And
 * none of them is a relation, so a region narrowed by the way is the region it was.
 */
class ATruthIsOneDemandHoweverItIsSpelledTest {

    private static final String MODEL = """
            module probe.truth

            data Amount = { flag: Bool, n: Int }

            behavior bare : (a: Amount) -> Bool
            let bare (a) = a.flag

            behavior equalToTrue : (a: Amount) -> Bool
            let equalToTrue (a) = a.flag == true

            behavior trueEqualTo : (a: Amount) -> Bool
            let trueEqualTo (a) = true == a.flag

            behavior unequalToFalse : (a: Amount) -> Bool
            let unequalToFalse (a) = a.flag /= false

            behavior deniedFalse : (a: Amount) -> Bool
            let deniedFalse (a) = Bool.not(a.flag == false)

            behavior denied : (a: Amount) -> Bool
            let denied (a) = Bool.not(a.flag)

            behavior equalToFalse : (a: Amount) -> Bool
            let equalToFalse (a) = a.flag == false

            behavior unequalToTrue : (a: Amount) -> Bool
            let unequalToTrue (a) = a.flag /= true

            behavior twoPositions : (a: Amount, b: Amount) -> Bool
            let twoPositions (a, b) = a.flag == b.flag
            """;

    private static final TermPath FLAG = TermPath.of("a").then("flag");

    @Test
    void everySpellingThatHoldsAtTrueIsTheTruthTrue() {
        for (String behavior : List.of("bare", "equalToTrue", "trueEqualTo", "unequalToFalse",
                "deniedFalse")) {
            assertEquals(new RowDemand.ATruth(FLAG, true), asked(behavior, true), behavior);
            assertEquals(new RowDemand.ATruth(FLAG, false), asked(behavior, false), behavior);
        }
    }

    @Test
    void everySpellingThatHoldsAtFalseIsTheTruthFalse() {
        for (String behavior : List.of("denied", "equalToFalse", "unequalToTrue")) {
            assertEquals(new RowDemand.ATruth(FLAG, false), asked(behavior, true), behavior);
            assertEquals(new RowDemand.ATruth(FLAG, true), asked(behavior, false), behavior);
        }
    }

    /** Two positions held against each other ask no one value of either, and are declined as
     *  before. */
    @Test
    void twoPositionsComparedAreNoTruth() {
        assertInstanceOf(OnTheWay.Declined.class, stated("twoPositions", true));
    }

    /** What a region is narrowed by is what it can measure, and a truth is not that. */
    @Test
    void aTruthLeavesTheRegionWhereItWas() {
        SearchRegion before = reading("bare").quantities().region();
        WayToTheBorder way = new WayToTheBorder(List.of(stated("bare", true)));
        assertSame(before, way.narrowing(before));
    }

    private static RowDemand.OfACondition asked(String behavior, boolean holding) {
        return assertInstanceOf(OnTheWay.TakenIn.class, stated(behavior, holding)).demand();
    }

    /** What {@code behavior}'s body asks of a row coming out {@code holding}. */
    private static OnTheWay stated(String behavior, boolean holding) {
        AnalysisBody analysis = analysis(behavior);
        InputReading reading = reading(behavior);
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs(behavior).parameterReads(),
                reading.declared(), ElementBindings.of(analysis, rules().newtypes()));
        List<OnTheWay> stated = ReachingCuts.stating(Condition.of(analysis.core(), reads,
                        rules().symbols(), rules().newtypes(),
                        new ConditionNumbering(module(), behavior)),
                reading, holding);
        assertEquals(1, stated.size(), () -> "one condition: " + stated);
        return stated.getFirst();
    }

    private static AnalysisBody analysis(String behavior) {
        Bodies.Elaborated checked =
                COMPILATION.db().ask(new Bodies.Checked(module())).value();
        assertNotNull(checked, () -> "the model under test compiles: "
                + COMPILATION.diagnostics().values().stream().flatMap(List::stream)
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                .toList());
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        assertNotNull(analysis, () -> "the model under test writes " + behavior);
        return analysis;
    }

    private static InputDomain inputs(String behavior) {
        InputDomain inputs = COMPILATION.db().ask(new Adequacy.Inputs(module())).value()
                .get(behavior);
        assertNotNull(inputs, "the model under test compiles");
        return inputs;
    }

    private static InputReading reading(String behavior) {
        return inputs(behavior).reading(rules());
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
