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
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * How many an operation answers, where which number that is turns on how its arguments stand, is
 * read in each case of it: a comparison over it is the comparison of what each case says, where
 * the arguments stand as that case says.
 *
 * <p>Held to what the comparison comes to: what it asks of a row, read both ways round, is taken
 * of every way the numbers it turns on can stand here and has to come out as the comparison does
 * there — {@code List.take} answering as many as were asked for where there are that many, all of
 * them where there are fewer, and none where none were asked for.
 */
class ASizeThatTurnsOnHowTheArgumentsStandIsReadInEachCaseTest {

    private static final String MODEL = """
            module probe.sizes

            data Basket = { items: List<Int>, wanted: Int }

            behavior enough : (b: Basket) -> Bool
            let enough (b) = List.length(List.take(b.wanted, b.items)) >= 2
            """;

    private static final TermPath ITEMS = TermPath.of("b").then("items");
    private static final TermPath WANTED = TermPath.of("b").then("wanted");

    @Test
    void whatTheComparisonAsksComesOutAsItDoesWhereverTheNumbersStand() {
        for (boolean holding : List.of(true, false)) {
            List<OnTheWay> asked = statedAll("enough", holding);
            List<String> wrong = new ArrayList<>();
            for (long wanted : List.of(-1L, 0L, 1L, 2L, 3L, 5L)) {
                for (long items = 0; items <= 4; items++) {
                    boolean comesOut = Math.min(Math.max(wanted, 0), items) >= 2;
                    if (holds(asked, wanted, items) != (comesOut == holding)) {
                        wrong.add("wanted " + wanted + " of " + items);
                    }
                }
            }
            assertEquals(List.of(), wrong, () -> "coming out " + holding + ": " + asked);
        }
    }

    /** Whether every one of {@code asked} holds where the basket holds {@code items} and asks for
     *  {@code wanted}. */
    private static boolean holds(List<OnTheWay> asked, long wanted, long items) {
        return asked.stream().allMatch(each -> holds(each, wanted, items));
    }

    private static boolean holds(OnTheWay asked, long wanted, long items) {
        return switch (asked) {
            case OnTheWay.TakenIn taken -> switch (taken.demand()) {
                case RowDemand.Relational(TakenConstraint.Affine(var form, var rel)) -> {
                    BigInteger sum = whole(form.constant());
                    for (var term : form.coefs().entrySet()) {
                        long value = switch (term.getKey()) {
                            case NumericTerm.ValueOf(TermPath at) when at.equals(WANTED) -> wanted;
                            case NumericTerm.TakenOf size when size.subjectPath().equals(ITEMS) ->
                                    items;
                            default -> throw new AssertionError("a number the model does not"
                                    + " turn on: " + term.getKey());
                        };
                        sum = sum.add(whole(term.getValue()).multiply(BigInteger.valueOf(value)));
                    }
                    yield rel.holds(sum.signum());
                }
                case RowDemand.Relational _, RowDemand.Exists _, RowDemand.ForAll _,
                     RowDemand.ATruth _, RowDemand.SoMany _, RowDemand.ForTheRun _ ->
                        throw new AssertionError("a size is asked as numbers are: " + asked);
            };
            case OnTheWay.OneOf one -> one.alternatives().stream()
                    .anyMatch(each -> holds(each, wanted, items));
            case OnTheWay.Settled settled -> settled.thisWay();
            case OnTheWay.Narrowed _, OnTheWay.Declined _ ->
                    throw new AssertionError("a size in cases is read whole: " + asked);
        };
    }

    private static BigInteger whole(ExactRatio ratio) {
        if (!(ratio.floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger whole))
                || !ratio.isWhole()) {
            throw new AssertionError("a size is counted in whole numbers: " + ratio);
        }
        return whole;
    }

    private static List<OnTheWay> statedAll(String behavior, boolean holding) {
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
                reading, holding, WhatConditionsState.of(reading));
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
