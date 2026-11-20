package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.inputs.AStopShown;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.AStopNotShown;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.RuleWhereARunMayStop;
import souther.compiler.inputs.RuleWhereAStopIsNotShown;
import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.inputs.WhatIsShownOfAStop;
import souther.compiler.inputs.WhyAStopIsNotShown;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;

import java.math.BigInteger;
import java.util.Comparator;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What is shown of a run stopping at a rule is said of the rule: that one does where a value of
 * the input is shown to exist that stops it, that whether one does is not resolved where neither
 * that nor that none does is shown, both where both hold of its operations, and nothing where
 * no run stops in it. Whatever places the rule is filed at, and each rule once for each.
 */
class WhatIsShownOfAStopIsSaidOfTheRuleTest {

    /** A total of the elements files the rule at no place, and its stop is not resolved all the
     *  same: no value of the elements is put to it. */
    @Test
    void aTotalOfTheElementsIsNotResolvedThoughTheRuleIsFiledNowhere() {
        assertEquals(List.of(RuleWhereAStopIsNotShown.class),
                kinds(compiled("ds: List<Int>", "if List.sum(ds) >= 10 then 1 else 2")));
    }

    /** The same, added up by a walk. */
    @Test
    void aWalkAddingUpTheElementsIsNotResolvedThoughTheRuleIsFiledNowhere() {
        assertEquals(List.of(RuleWhereAStopIsNotShown.class), kinds(compiled("ds: List<Int>",
                "if List.fold((w, l) -> w + l, 0, ds) >= 10 then 1 else 2")));
    }

    /** An operation on an arm of a choice, read and put on the way with the arm's condition, is
     *  not resolved, of the rule, and holds no border: which rows get past it is read. */
    @Test
    void anUnresolvedStopOfAnOperationReadIsSaidOfTheRuleAndHoldsNoBorder() {
        Compilation compilation = compiled("q: Int",
                "if (if q > 5 then q + 1 else 3) >= q then 1 else 2");
        List<WhatIsShownOfAStop> shown = stopsShown(compilation);
        assertEquals(List.of(RuleWhereAStopIsNotShown.class), kinds(shown));
        assertEquals(List.of(new AStopNotShown(Optional.of("q + 1"), WhyAStopIsNotShown.ON_AN_ARM)),
                ((RuleWhereAStopIsNotShown) shown.getFirst()).notShown());
        assertFalse(holdsABorderOpen(compilation));
    }

    /** An operation over what a walk comes to, which the way does not keep within its type, is
     *  not resolved, of the rule, and holds the border of the place it is filed at as well:
     *  which rows get past it is not read. */
    @Test
    void anUnresolvedStopOverAValueWorkedOutIsSaidOfTheRuleAndOfThePlace() {
        Compilation compilation = compiled("ds: List<Int>, q: Int", "if List.fold((w, l) -> "
                + "if l > w then l else w, 0, ds) + 1 <= q then 1 else 2");
        assertEquals(List.of(RuleWhereAStopIsNotShown.class), kinds(compilation));
        assertTrue(holdsABorderOpen(compilation));
    }

    /** A product of two numbers of the input is no form a value is put to, so whether it stops
     *  a run is not resolved; and its line stands, the border held by nothing. */
    @Test
    void aProductNotResolvedLeavesItsLineStanding() {
        Compilation compilation = compiled("price: Int, quantity: Int",
                "if 2 * price * quantity >= 1000 then 1 else 2");
        assertEquals(List.of(RuleWhereAStopIsNotShown.class), kinds(compilation));
        assertFalse(holdsABorderOpen(compilation));
    }

    /** {@code 2 * q} stops every run at {@code q} past the half of the greatest Int, which a
     *  value of the input reaches: a stop shown, with where every run stops. And no line is
     *  drawn at the greatest Int, where {@code 2 * q - q} would come to it: no run gets past
     *  {@code 2 * q} there. */
    @Test
    void anOperationBeforeTheOneTheComparisonStatesIsAStopShown() {
        Compilation compilation = compiled("q: Int",
                "if 2 * q - q >= 9223372036854775807 then 1 else 2");
        List<WhatIsShownOfAStop> shown = stopsShown(compilation);
        assertEquals(List.of(RuleWhereARunMayStop.class), kinds(shown));
        assertFalse(((RuleWhereARunMayStop) shown.getFirst()).everyRunStops().isEmpty());
        assertEquals(List.of(), linesAtTheGreatestInt(compilation));
        // And the same comparison of q with nothing before it stopping a run there is drawn.
        assertEquals(List.of("9223372036854775807"), linesAtTheGreatestInt(compiled("q: Int",
                "if q - 1 >= 9223372036854775806 then 1 else 2")));
    }

    private static List<String> linesAtTheGreatestInt(Compilation compilation) {
        return compilation.db().ask(new Adequacy.Boundaries("w1", "m")).value().stream()
                .map(BorderAssessment::value).filter("9223372036854775807"::equals).toList();
    }

    /** Where every run on an application stops is proved, and no run is shown to make the
     *  application there: the proof is kept with the stop not resolved. */
    @Test
    void whereEveryRunStopsIsKeptWhereNoRunIsShownToGetThere() {
        List<WhatIsShownOfAStop> shown = stopsShown(compiled("ds: List<Int>",
                "if List.all(x -> x + 10 > 3, ds) then 1 else 2"));
        assertEquals(List.of(RuleWhereAStopIsNotShown.class), kinds(shown));
        assertFalse(((RuleWhereAStopIsNotShown) shown.getFirst()).everyRunStops().isEmpty());
    }

    /** A comparison every run getting to which stops in its sides is one runs get to: where the
     *  declarations hold the number at the greatest Int, what is worked out of it is no
     *  operation shown to stop no run, and is said at least as not resolved, never as
     *  nothing. */
    @Test
    void anOperationTheDeclarationsTakePastItsTypeIsNeverSafe() {
        Compilation compilation = ACompiledModel.answered("""
                module w1
                data MaxInt = Int invariant value == 9223372036854775807
                behavior m : (q: MaxInt) -> Int
                let m (q) = if q.value + 1 > 3 then 1 else 2
                """);
        assertFalse(stopsShown(compilation).isEmpty(), () -> divided(compilation)
                .rulesWithoutALine().toString());
    }

    /** An operation every value of what it is over takes past its type, over a number whose
     *  least is above the least Int: every length of a string, nought included, takes the second
     *  addition past it. The rows past its ends are every row there is, which is rows. */
    @Test
    void anOperationEveryLengthTakesPastItsTypeIsNeverSafe() {
        assertFalse(kinds(compiled("s: String",
                "if (String.length(s) + 1) + 9223372036854775807 > 3 then 1 else 2")).isEmpty());
    }

    /** The same, where every length but nought takes it past. */
    @Test
    void anOperationSomeLengthsTakePastItsTypeIsNeverSafe() {
        assertFalse(kinds(compiled("s: String",
                "if String.length(s) + 9223372036854775807 > 3 then 1 else 2")).isEmpty());
    }

    /** A stop the way rules out is no stop, said neither as one nor as one not resolved. */
    @Test
    void aStopTheWayRulesOutIsNothingSaid() {
        assertEquals(List.of(), kinds(compiled("q: Int", "if q < 0 && q + 10 > 3 then 1 else 2")));
    }

    /** What a construction on the way asks of a run, which an admissible value on the way does
     *  not meet, is a stop shown, resting on that value, and nothing is left unresolved. */
    @Test
    void whatAConstructionAsksThatAValueOnTheWayDoesNotMeetIsAStop() {
        Compilation compilation = ACompiledModel.answered("""
                module w1
                data Refund = Decimal invariant value >= 0.0m
                data Out = { refund: Refund, within: Bool }
                behavior m : (gross: Decimal, limit: Decimal) -> Out constructs Out, Refund
                let m (gross, limit) = Out {
                    refund = Refund(gross),
                    within = Decimal.compare(gross, limit) <= 0
                }
                """);
        List<WhatIsShownOfAStop> shown = stopsShown(compilation);
        assertEquals(List.of(RuleWhereARunMayStop.class), kinds(shown));
        RuleWhereARunMayStop stops = (RuleWhereARunMayStop) shown.getFirst();
        assertTrue(stops.shown().isEmpty());
        assertEquals(1, stops.constructions().size());
        assertEquals(List.of(new AStopShown.NumberAt(TermPath.of("gross"),
                BigInteger.ONE.negate())), stops.constructions().getFirst().at());
    }

    /** What a construction on the way asks of a run, where something worked out before it may
     *  end the run first, is said as not resolved and never as a stop. */
    @Test
    void whatAConstructionAsksAfterSomethingThatMayEndTheRunIsNotResolved() {
        Compilation compilation = ACompiledModel.answered("""
                module w1
                data Count = Int invariant value >= 0
                data Out = { n: Count, within: Bool }
                behavior m : (x: Int, c: Int) -> Out constructs Out, Count
                let m (x, c) = Out { n = Count(x + 1), within = x <= c }
                """);
        List<WhatIsShownOfAStop> shown = stopsShown(compilation);
        assertEquals(List.of(RuleWhereAStopIsNotShown.class), kinds(shown));
        RuleWhereAStopIsNotShown open = (RuleWhereAStopIsNotShown) shown.getFirst();
        assertFalse(open.asks().isEmpty());
        assertTrue(open.notShown().isEmpty());
    }

    /** A rule read at two calls of the helper it is written in: at the first, nothing comes
     *  before it and a run stops in it; at the second, the first may stop a run first, and
     *  whether this one does is not resolved. Both are said of the one rule. */
    @Test
    void aStopShownBesideOneNotResolvedIsSaidAsBoth() {
        assertEquals(List.of(RuleWhereARunMayStop.class, RuleWhereAStopIsNotShown.class),
                kinds(ACompiledModel.answered("""
                        module w1
                        let over (n: Int) = n + 1 > 3
                        behavior m : (q: Int, r: Int) -> Int
                        let m (q, r) = if over(q) && over(r) then 1 else 2
                        """)));
    }

    /** An operation every row on the way keeps within its type has nothing said of it. */
    @Test
    void anOperationTheWayKeepsWithinItsTypeHasNothingSaid() {
        assertEquals(List.of(), kinds(compiled("q: Int",
                "if q < 100 && q > -100 && q + 1 > 0 then 1 else 2")));
    }

    /** An operation past its type on a value of the input that exists and gets there is said as
     *  a stop and nothing else. */
    @Test
    void anOperationPastItsTypeOnTheWayIsAStop() {
        List<WhatIsShownOfAStop> shown = stopsShown(compiled("q: Int",
                "if q > 0 && q + 1 > 3 then 1 else 2"));
        assertEquals(List.of(RuleWhereARunMayStop.class), kinds(shown));
        // And it carries what shows it: the operation, and the value of q it stops at.
        assertEquals(List.of(new AStopShown("q + 1", List.of(new AStopShown.NumberAt(
                        TermPath.of("q"), BigInteger.valueOf(Long.MAX_VALUE))))),
                ((RuleWhereARunMayStop) shown.getFirst()).shown());
    }

    /** One rule read at three calls, two of which leave its stop unresolved, is one finding of
     *  each kind, with every place it was read at. */
    @Test
    void oneRuleReadAtSeveralCallsIsOneFindingOfEachKind() {
        List<WhatIsShownOfAStop> shown = stopsShown(ACompiledModel.answered("""
                module w1
                let over (n: Int) = n + 1 > 3
                behavior m : (q: Int, r: Int, s: Int) -> Int
                let m (q, r, s) = if over(q) && over(r) && over(s) then 1 else 2
                """));
        assertEquals(List.of(RuleWhereARunMayStop.class, RuleWhereAStopIsNotShown.class),
                kinds(shown));
        RuleWhereAStopIsNotShown open = shown.stream()
                .filter(RuleWhereAStopIsNotShown.class::isInstance)
                .map(RuleWhereAStopIsNotShown.class::cast).findFirst().orElseThrow();
        assertEquals(List.of(WhyAStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP),
                open.notShown().stream().map(AStopNotShown::why).distinct().toList());
    }

    /** Whether what a run works out to evaluate a rule holds the border of a place it is filed
     *  at. */
    private static boolean holdsABorderOpen(Compilation compilation) {
        return divided(compilation).rulesWithoutALine().stream().map(RuleWithoutALine::why)
                .anyMatch(BlockReason.EvaluationStopsNotFullyRead.class::isInstance);
    }

    private static List<Class<?>> kinds(Compilation compilation) {
        return kinds(stopsShown(compilation));
    }

    private static List<Class<?>> kinds(List<WhatIsShownOfAStop> shown) {
        return shown.stream().<Class<?>>map(Object::getClass)
                .sorted(Comparator.comparing(Class::getSimpleName)).toList();
    }

    private static List<WhatIsShownOfAStop> stopsShown(Compilation compilation) {
        return divided(compilation).stopsShown();
    }

    private static Partitions.Partitioning divided(Compilation compilation) {
        Partitions.Partitioning divided =
                compilation.db().ask(new Adequacy.Divided("w1", "m")).value();
        assertNotNull(divided, "m was divided");
        return divided;
    }

    private static Compilation compiled(String parameters, String body) {
        return ACompiledModel.answered("""
                module w1
                behavior m : (%s) -> Int
                let m (%s) = %s
                """.formatted(parameters, parameters.replaceAll(":\\s*[A-Za-z<>]+", ""), body));
    }
}
