package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.CountsWrittenOut;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.OnOneElement;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a case chosen part by part puts on the way at a comparison, joined from what each of its
 * parts asks ({@link ReachingCuts#whereItDecides(Condition, Proposition, InputReading,
 * Function, RemaindersOfAnElement.Kept)}), is what reading the case whole puts there: the same
 * entries in the same order, each put by the same copies of the model's code, and declined where
 * the whole is.
 *
 * <p>Asked as a comparison asks them, one case after another through the same parts kept and the
 * same remainders kept, so that a part met in one case is taken as it was read there in the
 * next. Over the shapes that make joining differ from reading whole if it were wrong: a statement
 * following from two parts put between the parts, a part chosen again as what the others leave of
 * it, a part met at another place, a choice and a count among the parts, a part with no words,
 * and a conjunction that writing out its counts changes.
 */
class WhatACaseChosenPartByPartPutsOnTheWayIsWhatItPutsWholeTest {

    /** The comparison {@code floorMod(a + n, 7) == 0} over the elements {@code n} of
     *  {@code List.rangeInclusive(0, days)}, the reading it was read against, and its numbers. */
    private record Read(ComparisonReadings.Reading comparison, InputReading reading,
                        Quantity.OfABinding element, Quantity a,
                        Quantity.RemainderOfADividend remainder) {}

    private static final Read READ = read();

    private static final TermPath XS = TermPath.of("xs");

    /** What each case put on the way, joined and whole, once all are asked. */
    private record Asked(List<ReachingCuts.Stating> each, int partsRead) {}

    /**
     * Each of {@code cases} put on the way joined from its parts, through one keeping of the parts
     * and one of what follows, as the cases of a comparison are — each held to what reading it
     * whole puts there.
     */
    private static Asked assertPutAsWhole(Proposition... cases) {
        Map<Proposition, ReachingCuts.Stating> parts = new HashMap<>();
        int[] read = {0};
        Function<Proposition, ReachingCuts.Stating> eachPart = part ->
                parts.computeIfAbsent(part, asked -> {
                    read[0]++;
                    return READ.comparison().aPartAsked(asked, READ.reading());
                });
        RemaindersOfAnElement.Kept followed = new RemaindersOfAnElement.Kept();
        List<ReachingCuts.Stating> out = new ArrayList<>();
        for (Proposition decides : cases) {
            ReachingCuts.Stating whole = READ.comparison().aCasePutOnTheWay(decides,
                    READ.reading());
            ReachingCuts.Stating joined = READ.comparison().aCasePutOnTheWay(decides,
                    READ.reading(), eachPart, followed);
            assertEquals(whole.entries(), joined.entries(), decides::toString);
            assertEquals(List.copyOf(whole.by().entries().entrySet()),
                    List.copyOf(joined.by().entries().entrySet()),
                    () -> "who put each entry, in order: " + decides);
            out.add(whole);
        }
        return new Asked(out, read[0]);
    }

    /**
     * Where the element is held to a class beside a statement weighing it in its remainders, what
     * follows is put just past that statement, ahead of the parts chosen after it, and is put by
     * whoever put the statements it follows from. The same statement beside another class leaves
     * another remainder.
     */
    @Test
    void whatFollowsFromTwoPartsIsPutBetweenThePartsAsWhole() {
        Proposition weighing = remainderOf(1, READ.a(), 0, 7, 0);
        Proposition other = atLeast(READ.a(), 2);
        Proposition turn = remainderOf(1, null, 3, 7, 0);
        Asked asked = assertPutAsWhole(Proposition.all(List.of(weighing, other)),
                Proposition.all(List.of(weighing, other, remainderOf(1, null, 5, 7, 0))),
                Proposition.all(List.of(weighing, other, turn)));
        List<OnTheWay> put = asked.each().getLast().entries();
        int follows = -1;
        for (int at = 0; at < put.size(); at++) {
            if (put.get(at) instanceof OnTheWay.TakenIn(var _, RowDemand.OnARemainder _)) {
                follows = at;
            }
        }
        assertTrue(follows >= 0 && follows < put.size() - 1,
                () -> "what follows is put between the parts: " + put);
    }

    /** A part chosen again as what the parts beside it leave of it is another part, and is read;
     *  a part read for a case before is not read again. */
    @Test
    void aPartChosenAgainAsAnotherIsReadAndOneReadBeforeIsNot() {
        Proposition first = atLeast(READ.element(), 1);
        Proposition again = atLeast(READ.element(), 2);
        Proposition other = atLeast(READ.a(), 2);
        Proposition weighing = remainderOf(1, READ.a(), 0, 7, 0);
        Asked asked = assertPutAsWhole(Proposition.all(List.of(first, other)),
                Proposition.all(List.of(again, other, weighing)),
                Proposition.all(List.of(again, other, weighing, remainderOf(1, null, 3, 7, 0))));
        assertEquals(5, asked.partsRead(), "each part read once, in whichever case it was met");
    }

    /** The same parts at other places and beside other parts are put where they stand, each
     *  following statement naming the statements it follows from. */
    @Test
    void thePartsAtOtherPlacesArePutWhereTheyStandAsWhole() {
        Proposition weighing = remainderOf(1, READ.a(), 0, 7, 0);
        Proposition other = atLeast(READ.a(), 2);
        Proposition turn = remainderOf(1, null, 3, 7, 0);
        Proposition element = atLeast(READ.element(), 1);
        assertPutAsWhole(Proposition.all(List.of(other, weighing)),
                Proposition.all(List.of(weighing, other)),
                Proposition.all(List.of(turn, element, other, weighing)),
                Proposition.all(List.of(weighing, element, other, turn)),
                Proposition.all(List.of(other, turn, weighing)));
    }

    @Test
    void aChoiceAndACountAmongThePartsArePutAsWhole() {
        Proposition choice = Proposition.any(List.of(atLeast(READ.a(), 5), atMost(READ.a(), -5)));
        Proposition count = new Proposition.SoManyHold(List.of(atLeast(READ.a(), 1),
                atLeast(READ.a(), 3)), List.of(1, 1), List.of(1));
        Asked asked = assertPutAsWhole(
                Proposition.all(List.of(remainderOf(1, READ.a(), 0, 7, 0), choice)),
                Proposition.all(List.of(remainderOf(1, READ.a(), 0, 7, 0), choice, count,
                        remainderOf(1, null, 3, 7, 0))));
        List<OnTheWay> put = asked.each().getLast().entries();
        assertTrue(put.stream().anyMatch(OnTheWay.OneOf.class::isInstance), put::toString);
        assertTrue(put.stream().anyMatch(OnTheWay.Counted.class::isInstance), put::toString);
    }

    @Test
    void aPartWithNoWordsIsDeclinedAsWhole() {
        Proposition unread = new Proposition.Unread(Optional.empty(), 0,
                new WhyUnread.NoNumberOnARun(), false, true);
        Asked asked = assertPutAsWhole(Proposition.all(List.of(unread, atLeast(READ.a(), 2))),
                Proposition.all(List.of(remainderOf(1, READ.a(), 0, 7, 0), unread,
                        atLeast(READ.a(), 2), remainderOf(1, null, 3, 7, 0))));
        assertTrue(asked.each().getLast().entries().stream()
                .anyMatch(OnTheWay.Declined.class::isInstance), "declined where the whole is");
    }

    /** A conjunction writing out its counts changes is what it is written out as, which is read
     *  whole: no part of it is asked by itself. */
    @Test
    void aConjunctionWritingOutItsCountsChangesIsReadWhole() {
        Proposition inAnElement = new Proposition.Some(new DecisionSubject.AnInput(XS),
                new Proposition.SoManyHold(List.of(atLeast(READ.a(), 1),
                        new Proposition.Truth(new DecisionSubject.AnInput(XS.element()), true)),
                        List.of(1, 1), List.of(1)), true);
        Proposition decides = Proposition.all(List.of(inAnElement, atLeast(READ.a(), 2)));
        CountsWrittenOut.Written written = assertInstanceOf(CountsWrittenOut.Written.class,
                CountsWrittenOut.outsideElementsOf(decides));
        assertNotSame(decides, written.stated(), "writing out the count changes the conjunction");
        assertEquals(0, assertPutAsWhole(decides).partsRead());
    }

    /** {@code floorMod(weight·n + over + constant, divisor) == left}, {@code over} left out where
     *  null. */
    private static Proposition remainderOf(int weight, Quantity over, int constant, int divisor,
                                           int left) {
        Map<Quantity, ExactRatio> dividend = new LinkedHashMap<>();
        dividend.put(READ.element(), ExactRatio.of(weight));
        if (over != null) {
            dividend.put(over, ExactRatio.ONE);
        }
        Quantity remainder = new Quantity.RemainderOfADividend(READ.remainder().operation(),
                new LinearForm<>(ExactRatio.of(constant), dividend), BigInteger.valueOf(divisor));
        return compared(new LinearForm<>(ExactRatio.of(-left), Map.of(remainder, ExactRatio.ONE)),
                Rel.EQ);
    }

    private static Proposition atLeast(Quantity of, int least) {
        return compared(new LinearForm<>(ExactRatio.of(-least), Map.of(of, ExactRatio.ONE)),
                Rel.GE);
    }

    private static Proposition atMost(Quantity of, int most) {
        return compared(new LinearForm<>(ExactRatio.of(-most), Map.of(of, ExactRatio.ONE)),
                Rel.LE);
    }

    private static Proposition compared(LinearForm<Quantity> form, Rel rel) {
        Relation.OneWay<Quantity> one = Relation.OneWay.of(form, rel);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds());
    }

    private static Read read() {
        Compilation compilation = Compilation.ofSource("""
                module w1
                behavior m : (a: Int, days: Int, xs: List<Bool>) -> Bool
                let m (a, days, xs) = List.any(n -> Int.floorMod(a + n, 7) == 0,
                                               List.rangeInclusive(0, days))
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        String module = compilation.modules().getFirst();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get("m");
        AnalysisBody analysis = checked.analysisBodies().get("m");
        InputReading read = inputs.reading(rules);
        List<ComparisonReadings.Reading> readings = ComparisonReadings.of("m", analysis, read,
                InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                        inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                        inputs.dependencies()),
                CountWitnesses.AtComparisons.NONE).comparisons();
        ComparisonReadings.Reading last = readings.getLast();
        if (!(last.statement() instanceof ComparisonReadings.Stated.AComparison(var comparison))) {
            throw new AssertionError("the last statement is a comparison: " + last);
        }
        Proposition stated = WhatConditionsState.of(read).comparison(comparison, last.reads(), read)
                .stated().proposition();
        Quantity.OfABinding element = OnOneElement.theElementOf(stated).orElseThrow();
        if (!(stated instanceof Proposition.Compared(Relation.Affine(var form, var _), var _,
                var _)) || !(form.coefs().keySet().iterator().next()
                instanceof Quantity.RemainderOfADividend remainder)) {
            throw new AssertionError("the comparison weighs a remainder: " + stated);
        }
        Quantity a = remainder.dividend().coefs().keySet().stream()
                .filter(DecisionAtom.OfTheInput.class::isInstance).findFirst().orElseThrow();
        return new Read(last, read, element, a, remainder);
    }
}
