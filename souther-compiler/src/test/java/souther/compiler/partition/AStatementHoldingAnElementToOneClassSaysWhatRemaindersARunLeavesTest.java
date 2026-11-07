package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.WholeNumberRuns;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A case of where a line decides whose statements only a run checks hold its element to one
 * class, and weigh it elsewhere only in a remainder coming round as often, says what remainder of
 * the input's numbers a run passing them leaves: {@code floorMod(n + 5, 7) = 0} holds {@code n}
 * at 2 round 7, so {@code floorMod(d - a + n + 6, 7) = 0} leaves {@code floorMod(d - a, 7)} at 6
 * on every element that passes. Held beside a remainder of the input that leaves another, the way
 * is one no row takes, and the statements that prove it are the case's own.
 *
 * <p>Only what follows from one case's statements, read at one element: a class stated elsewhere
 * on the way, a case weighing two elements, a class the input decides, or a remainder coming round
 * over more elements than the class's members are apart says nothing, and the way stays open —
 * which proves nothing of it.
 */
class AStatementHoldingAnElementToOneClassSaysWhatRemaindersARunLeavesTest {

    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("m",
                    new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 0));
    private static final NumericTerm A = new NumericTerm.ValueOf(TermPath.of("r").then("a"));
    private static final NumericTerm D = new NumericTerm.ValueOf(TermPath.of("r").then("d"));
    private static final NumericTerm DAYS = new NumericTerm.ValueOf(TermPath.of("r").then("days"));
    private static final ValueName FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");
    private static final Quantity.OfABinding N = element("f");
    private static final Quantity.OfABinding OTHER = element("g");

    /** Two round 7 puts the day at 6 round 7, which the line's point does not leave. */
    @Test
    void anElementHeldToOneClassPutsTheRemainderItWeighsAtOneOfTheInput() {
        OnTheWay turn = turn(N, 5);
        OnTheWay sunday = sunday(N, 7);
        OnTheWay point = inputLeaves(7, 1);
        Reachability.NumbersLeaveNone closed = assertClosed(way(List.of(turn, sunday), point));
        assertEquals(List.of(demand(turn), demand(sunday), demand(point)), closed.statements(),
                "the remainder read off two statements is said as those two");
    }

    @Test
    void whatFollowsStandsBesideTheStatementsAndNotInTheirPlace() {
        OnTheWay turn = turn(N, 5);
        OnTheWay sunday = sunday(N, 7);
        List<OnTheWay> put = withWhatFollows(List.of(turn, sunday));
        assertEquals(3, put.size(), () -> "both statements, and what follows: " + put);
        assertEquals(List.of(turn, sunday), put.subList(0, 2));
        RowDemand.OnARemainder follows = assertInstanceOf(RowDemand.OnARemainder.class,
                demand(put.get(2)));
        assertEquals(Optional.of(WholeNumberRuns.one(BigInteger.valueOf(6), BigInteger.valueOf(6))),
                ofTheInput().leftBy(follows), "floorMod(d - a + 8, 7) at nought is d - a at 6");
        assertEquals(List.of(demand(turn), demand(sunday)), follows.from());
    }

    @Test
    void whereTheInputLeavesTheRemainderTheStatementsDoTheWayIsOpen() {
        assertOpen(way(List.of(turn(N, 5), sunday(N, 7)), inputLeaves(7, 6)));
    }

    @Test
    void whicheverOrderTheCaseSaysThemInTheyAreReadTogether() {
        assertClosed(way(List.of(sunday(N, 7), turn(N, 5)), inputLeaves(7, 1)));
    }

    @Test
    void withoutAClassTheElementIsNotPutAnywhere() {
        assertOpen(way(List.of(sunday(N, 7)), inputLeaves(7, 1)));
    }

    /** A class stated on the way and not by the case may be of the binding at another
     *  application: it is not read beside the case. */
    @Test
    void aClassStatedElsewhereOnTheWayIsNotReadBesideTheCase() {
        List<OnTheWay> onTheWay = new ArrayList<>();
        onTheWay.add(turn(N, 5));
        onTheWay.addAll(withWhatFollows(List.of(sunday(N, 7))));
        onTheWay.add(inputLeaves(7, 1));
        assertOpen(onTheWay);
    }

    /** A case weighing two elements is not read at one of them. */
    @Test
    void aCaseWeighingTwoElementsSaysNothingOfEither() {
        assertOpen(way(List.of(turn(N, 5), sunday(N, 7), turn(OTHER, 3)), inputLeaves(7, 1)));
    }

    /** By 14 the remainder comes round over fourteen elements, and the class holds 2 and 9:
     *  {@code floorMod(d - a + n + 6, 14) = 0} leaves {@code floorMod(d - a, 14)} at 6 at the one
     *  and at 13 at the other, so the input leaving 13 is a way some element takes. */
    @Test
    void aRemainderComingRoundOverMoreElementsThanTheClassIsNotPutAtIt() {
        assertOpen(way(List.of(turn(N, 5), sunday(N, 14)), inputLeaves(14, 13)));
    }

    /** {@code floorMod(n + d, 7) = 0} holds the element to a class the input decides, which is
     *  no one class to put it at: put at nought, as though the input were not there, the day would
     *  be at 1 round 7 and the input leaving 2 a way no row takes, where the element at {@code -d}
     *  leaves the day wherever {@code a} puts it. */
    @Test
    void aClassTheInputDecidesIsNotPutAt() {
        Map<Quantity, ExactRatio> beside = new LinkedHashMap<>();
        beside.put(N, ExactRatio.ONE);
        beside.put(new DecisionAtom.OfTheInput(D), ExactRatio.ONE);
        assertOpen(way(List.of(forTheRun(remainder(beside, 0, 7), Rel.EQ, 0, true), sunday(N, 7)),
                inputLeaves(7, 2)));
    }

    /** That the remainder is not nought leaves six classes, which is no one class. */
    @Test
    void aClassDeniedIsNoOneClass() {
        assertOpen(way(List.of(forTheRun(remainder(Map.of(N, ExactRatio.ONE), 5, 7), Rel.EQ, 0,
                false), sunday(N, 7)), inputLeaves(7, 1)));
    }

    /** Weighed beside its remainder too, the element is not put at the class there, and the
     *  statement is not one of the input's numbers alone. */
    @Test
    void aStatementWeighingTheElementBesideItsRemainderIsNotPut() {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(remainder(sundayForm(N), 6, 7), ExactRatio.ONE);
        coefs.put(N, ExactRatio.ONE);
        Proposition stated = new Proposition.Compared(new Relation.Affine(
                new LinearForm<>(ExactRatio.of(-2), coefs), Rel.EQ), true);
        OnTheWay weighed = new OnTheWay.TakenIn(WHERE, new RowDemand.ForTheRun(stated,
                RowDemand.NoComposer.A_REMAINDER_OF_A_FORM, List.of(), Optional.empty()),
                NamedElements.NONE);
        assertOpen(way(List.of(turn(N, 5), weighed), inputLeaves(7, 1)));
    }

    /** Twice the element never leaves 1 by 4, and 2 round 7 and 3 round 7 share nothing: no
     *  condition on the input says either, and the run is left to find it. */
    @Test
    void aClassNoElementIsInIsLeftToTheRun() {
        OnTheWay odd = forTheRun(remainder(Map.of(N, ExactRatio.of(2)), 0, 4), Rel.EQ, 1, true);
        List<OnTheWay> alone = List.of(odd, sunday(N, 7));
        assertSame(alone, withWhatFollows(alone));
        List<OnTheWay> apart = List.of(turn(N, 5), turn(N, 4), sunday(N, 7));
        assertSame(apart, withWhatFollows(apart));
    }

    /** Inside an alternative the statement is put at the class the case holds the element to
     *  beside it: an alternative only Sunday takes is closed and one Monday takes is not. */
    @Test
    void aStatementInsideAnAlternativeIsPutAtTheClassBesideIt() {
        OnTheWay either = OnTheWay.OneOf.of(
                new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 1), WHERE,
                List.of(List.of(sunday(N, 7)), List.of(forTheRun(remainder(sundayForm(N), 6, 7),
                        Rel.EQ, 1, true))), Optional.empty());
        assertOpen(way(List.of(turn(N, 5), either), inputLeaves(7, 0)));
        OnTheWay neither = OnTheWay.OneOf.of(
                new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 1), WHERE,
                List.of(List.of(sunday(N, 7)), List.of(forTheRun(remainder(sundayForm(N), 6, 7),
                        Rel.EQ, 2, true))), Optional.empty());
        assertClosed(way(List.of(turn(N, 5), neither), inputLeaves(7, 2)));
    }

    /** What a point of a line on the input's remainder is searched at along the way: the way
     *  leaves it 6 round 7, so a row is composed there and at no other remainder. */
    @Test
    void theRemainderAWayLeavesAPointIsWhatFollowsFromTheCase() {
        Reachability.Reaching way = assertInstanceOf(Reachability.Reaching.class,
                Reachability.of(new WayToTheBorder(withWhatFollows(List.of(turn(N, 5),
                        sunday(N, 7)))), region()));
        assertEquals(Optional.of(WholeNumberRuns.one(BigInteger.valueOf(6), BigInteger.valueOf(6))),
                ofTheInput().leftAlong(way));
    }

    /** {@code floorMod(d - a, 7)}, unmoved. */
    private static ARemainderMoved ofTheInput() {
        return ARemainderMoved.of(new LinearForm<>(ExactRatio.ZERO,
                Map.of(D, ExactRatio.ONE, A, ExactRatio.of(-1))), BigInteger.valueOf(7))
                .orElseThrow();
    }

    /** {@code statements} put on the way as one case says them, and then {@code point}. */
    private static List<OnTheWay> way(List<OnTheWay> statements, OnTheWay point) {
        List<OnTheWay> out = new ArrayList<>(withWhatFollows(statements));
        out.add(point);
        return out;
    }

    /** {@code statements} with what follows, read as the entries of the case they say. */
    private static List<OnTheWay> withWhatFollows(List<OnTheWay> statements) {
        List<Proposition> parts = new ArrayList<>();
        statements.forEach(each -> statementsIn(each, parts));
        return RemaindersOfAnElement.withWhatFollows(Proposition.all(parts), statements);
    }

    private static void statementsIn(OnTheWay entry, List<Proposition> into) {
        if (entry instanceof OnTheWay.TakenIn(var _, RowDemand.ForTheRun run, var _, var _)) {
            into.add(run.statement());
        } else if (entry instanceof OnTheWay.OneOf several) {
            several.alternatives().forEach(way -> way.forEach(each -> statementsIn(each, into)));
        }
    }

    private static Reachability.NumbersLeaveNone assertClosed(List<OnTheWay> onTheWay) {
        WayToTheBorder way = new WayToTheBorder(onTheWay);
        Reachability read = Reachability.of(way, region());
        Reachability.NumbersLeaveNone numbers = assertInstanceOf(
                Reachability.NumbersLeaveNone.class, read,
                () -> "statements that leave no remainder in common are a way no row takes: "
                        + read);
        assertEquals(Optional.of(new NoInputTakesIt.TheConditionsClash(
                new NoInputTakesIt.Clash.RemaindersLeaveNone(numbers))),
                way.takenByNoInput(region(), () -> true));
        return numbers;
    }

    private static void assertOpen(List<OnTheWay> onTheWay) {
        WayToTheBorder way = new WayToTheBorder(onTheWay);
        assertInstanceOf(Reachability.Reaching.class, Reachability.of(way, region()));
        assertEquals(Optional.empty(), way.takenByNoInput(region(), () -> true));
    }

    private static RowDemand demand(OnTheWay entry) {
        return ((OnTheWay.TakenIn) entry).demand();
    }

    /** {@code floorMod(n + moved, 7) = 0}. */
    private static OnTheWay turn(Quantity.OfABinding element, long moved) {
        return forTheRun(remainder(Map.of(element, ExactRatio.ONE), moved, 7), Rel.EQ, 0, true);
    }

    /** {@code floorMod(d - a + n + 6, divisor) = 0}. */
    private static OnTheWay sunday(Quantity.OfABinding element, long divisor) {
        return forTheRun(remainder(sundayForm(element), 6, divisor), Rel.EQ, 0, true);
    }

    private static Map<Quantity, ExactRatio> sundayForm(Quantity.OfABinding element) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(element, ExactRatio.ONE);
        coefs.put(new DecisionAtom.OfTheInput(D), ExactRatio.ONE);
        coefs.put(new DecisionAtom.OfTheInput(A), ExactRatio.of(-1));
        return coefs;
    }

    private static Quantity.RemainderOfADividend remainder(Map<Quantity, ExactRatio> coefs,
                                                           long moved, long divisor) {
        return new Quantity.RemainderOfADividend(FLOOR_MOD,
                new LinearForm<>(ExactRatio.of(moved), coefs), BigInteger.valueOf(divisor));
    }

    /** That {@code remainder} comes out {@code rel} against {@code against}, or the other way. */
    private static OnTheWay forTheRun(Quantity.RemainderOfADividend remainder, Rel rel,
                                      long against, boolean holds) {
        Proposition stated = new Proposition.Compared(new Relation.Affine(
                new LinearForm<>(ExactRatio.of(-against), Map.of(remainder, ExactRatio.ONE)), rel),
                holds);
        return new OnTheWay.TakenIn(WHERE, new RowDemand.ForTheRun(stated,
                RowDemand.NoComposer.A_REMAINDER_OF_A_FORM, List.of(), Optional.empty()),
                NamedElements.NONE);
    }

    /** {@code floorMod(d - a, divisor) = remainder}, as the input is held at a line's point. */
    private static OnTheWay inputLeaves(long divisor, long remainder) {
        Quantity.RemainderOfADividend of = Quantity.RemainderOfADividend.ofTheInput(FLOOR_MOD,
                new LinearForm<>(ExactRatio.ZERO, Map.of(D, ExactRatio.ONE, A, ExactRatio.of(-1))),
                BigInteger.valueOf(divisor));
        return new OnTheWay.TakenIn(WHERE, new RowDemand.OnARemainder(of,
                WholeNumberRuns.one(BigInteger.valueOf(remainder), BigInteger.valueOf(remainder))),
                NamedElements.NONE);
    }

    /** The element of {@code rangeInclusive(0, r.days)} in the body of {@code definition}. */
    private static Quantity.OfABinding element(String definition) {
        return new Quantity.OfABinding(
                new BindingId(new BindingOwner.OfValue("m", definition), 0), List.of(), Type.INT,
                Optional.empty(), Optional.of(new Quantity.AWholeNumberInTurn(
                        LinearForm.constant(ExactRatio.ZERO),
                        new LinearForm<>(ExactRatio.ZERO, Map.of(DAYS, ExactRatio.ONE)))));
    }

    private static SearchRegion region() {
        Compilation compilation = Compilation.ofSource("""
                module m

                data R = { a: Int, d: Int, days: Int }
                data Yes

                behavior f : (r: R) -> Yes
                let f (r) = Yes
                """, "Main");
        var inputs = compilation.db().ask(new Adequacy.Inputs("m")).value().get("f");
        assertNotNull(inputs, "the model under test compiles");
        return inputs.reading(RuleReadings.of(compilation, "m")).quantities().region();
    }
}
