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
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * How many an operation answers, where its law says that is a number taken over the elements of
 * what it was handed, is read as that number: how many different values they come to, or what a
 * number of each adds up to — over the position the container stands at — and not as some other
 * number, or as nothing.
 *
 * <p>What a row is asked is then that number against the other side, which no composer writes a
 * container toward, so the run decides it; the statement is the one the law says.
 */
class ANumberOverTheElementsIsReadAsTheNumberItIsTest {

    private static final String MODEL = """
            module probe.overElements

            data Shelf = { codes: List<Int>, bins: List<List<Int>> }

            behavior varied : (s: Shelf) -> Bool
            let varied (s) = List.length(List.distinct(s.codes)) >= 2

            behavior stocked : (s: Shelf) -> Bool
            let stocked (s) = List.length(List.concat(s.bins)) >= 3
            """;

    private static final TermPath CODES = TermPath.of("s").then("codes");
    private static final TermPath BINS = TermPath.of("s").then("bins");

    @Test
    void howManyADistinctListHoldsIsHowManyDifferentValuesTheListHolds() {
        Quantity read = theOnlyNumber("varied");
        assertEquals(new Quantity.HowManyDifferent(CODES, CODES.element()), read);
    }

    @Test
    void howManyListsPutEndToEndHoldIsWhatTheirSizesAddUpTo() {
        Quantity.SumOver read = assertInstanceOf(Quantity.SumOver.class, theOnlyNumber("stocked"));
        assertEquals(BINS, read.container());
        assertEquals(0, read.ofTheElement().constant().signum(), () -> "nothing beside: " + read);
        Map.Entry<Quantity, ExactRatio> each = read.ofTheElement().coefs().entrySet().iterator()
                .next();
        assertEquals(1, read.ofTheElement().coefs().size(), () -> "one number of each: " + read);
        assertEquals(ExactRatio.ONE, each.getValue());
        NumericTerm.TakenOf size = assertInstanceOf(NumericTerm.TakenOf.class,
                assertInstanceOf(DecisionAtom.OfTheInput.class, each.getKey()).term());
        assertEquals(BINS.element(), size.subjectPath(), () -> "the size of each list: " + read);
    }

    /** The one number besides constants the condition {@code behavior} writes is compared over,
     *  as the run is asked it. */
    private static Quantity theOnlyNumber(String behavior) {
        List<OnTheWay> stated = statedAll(behavior);
        assertEquals(1, stated.size(), () -> "one statement: " + stated);
        RowDemand.ForTheRun run = assertInstanceOf(RowDemand.ForTheRun.class,
                assertInstanceOf(OnTheWay.TakenIn.class, stated.getFirst()).demand(),
                () -> "the run decides it: " + stated);
        assertEquals(RowDemand.NoComposer.A_NUMBER_OVER_ELEMENTS, run.why());
        Proposition.Compared compared = assertInstanceOf(Proposition.Compared.class,
                run.statement());
        LinearForm<Quantity> form = assertInstanceOf(Relation.Affine.class,
                compared.relation()).form();
        assertEquals(1, form.coefs().size(), () -> "one number: " + form);
        return form.coefs().keySet().iterator().next();
    }

    private static List<OnTheWay> statedAll(String behavior) {
        Bodies.Elaborated checked =
                COMPILATION.db().ask(new Bodies.Checked(module())).value();
        assertNotNull(checked, () -> "the model under test compiles: "
                + COMPILATION.diagnostics().values().stream().flatMap(List::stream)
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                .toList());
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        InputDomain inputs = COMPILATION.db().ask(new Adequacy.Inputs(module())).value()
                .get(behavior);
        InputReading reading = inputs.reading(rules());
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                reading.declared(), ElementBindings.of(analysis, rules().newtypes()),
                inputs.dependencies());
        return ReachingCuts.stating(Condition.of(analysis.core(), reads, rules().symbols(),
                        rules().newtypes(), new ConditionNumbering(module(), behavior)),
                reading, true, WhatConditionsState.of(reading));
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
