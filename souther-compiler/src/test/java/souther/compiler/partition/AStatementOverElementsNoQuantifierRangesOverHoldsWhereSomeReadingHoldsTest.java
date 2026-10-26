package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A statement whose positions are inside a container no quantifier of it ranges over is about the
 * row where one element is chosen in each such container, and it holds where some choice holds:
 * the choices are a product over the containers and each is one reading, so that what one
 * container's element chose is not what another's did.
 *
 * <p>Fails only where every choice was read and none held. Where there are more choices than a
 * point is tried against and none that was tried held, it could not be told.
 */
class AStatementOverElementsNoQuantifierRangesOverHoldsWhereSomeReadingHoldsTest {

    private static final String MODEL = """
            module g

            data A = { ok: Bool }

            data B = { ok: Bool }

            data Order = { flag: Bool, lines: List<B> }

            behavior decide : (xs: List<A>, ys: List<B>, orders: List<Order>) -> Int
            """;

    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12,
            souther.compiler.values.AsACompilationAllows.admittedValues(),
            souther.compiler.values.AsACompilationAllows.whatARuleLeaves());

    private static final TermPath AN_X = TermPath.of("xs").element().then("ok");

    private static final TermPath A_Y = TermPath.of("ys").element().then("ok");

    private static final TermPath AN_ORDERS_FLAG = TermPath.of("orders").element().then("flag");

    private static final TermPath A_LINE = TermPath.of("orders").element().then("lines")
            .element().then("ok");

    /** Some x and some y that hold: any of the one beside any of the other. */
    @Test
    void theElementsOfTwoContainersAreChosenApart() {
        Proposition both = truthOf(AN_X, A_Y);

        assertEquals(StandingAtAPoint.AtTheRow.HOLDS, at(both, as(false, true), bs(true, false)),
                "the second x with the first y, which a zip of the two would not read");
        assertEquals(StandingAtAPoint.AtTheRow.FAILS, at(both, as(false, false), bs(true)));
        assertEquals(StandingAtAPoint.AtTheRow.FAILS, at(both, as(true), bs()),
                "a container with nothing in it has no element to hold");
    }

    /** An order's flag and a line of that same order. */
    @Test
    void anElementOfAnInnerContainerIsChosenInsideTheOuterOne() {
        Proposition flaggedWithALine = truthOf(AN_ORDERS_FLAG, A_LINE);

        assertEquals(StandingAtAPoint.AtTheRow.FAILS, at(flaggedWithALine,
                orders(order(true, false), order(false, true))),
                "the flag of one order and the line of another is no reading");
        assertEquals(StandingAtAPoint.AtTheRow.HOLDS, at(flaggedWithALine,
                orders(order(false, false), order(true, false, true))));
    }

    /** A quantifier inside the statement chooses for itself and does not multiply the readings. */
    @Test
    void aQuantifierInsideTheStatementIsNotRangedOverAgain() {
        Proposition someX = new Proposition.Some(
                new DecisionSubject.AnInput(TermPath.of("xs")),
                new Proposition.Truth(new DecisionSubject.AnInput(AN_X), true), true);
        Proposition someXAndAY = Proposition.all(List.of(someX,
                new Proposition.Truth(new DecisionSubject.AnInput(A_Y), true)));

        assertEquals(StandingAtAPoint.AtTheRow.HOLDS,
                at(someXAndAY, as(false, true), bs(false, true)));
        assertEquals(StandingAtAPoint.AtTheRow.FAILS,
                at(someXAndAY, as(false, false), bs(true)));
        assertEquals(StandingAtAPoint.AtTheRow.FAILS,
                at(someXAndAY, as(true), bs(false, false)));
    }

    /**
     * More choices than a point is tried against: one that holds among those tried is a hold, and
     * none among them is not a fail while there are others that were not tried.
     */
    @Test
    void whereNotEveryReadingWasTriedNoneHoldingIsNotAFail() {
        Proposition both = truthOf(AN_X, A_Y);
        List<Boolean> many = new ArrayList<>();
        for (int i = 0; i < 300; i++) {
            many.add(false);
        }
        List<Boolean> holdsFirst = new ArrayList<>(many);
        holdsFirst.set(0, true);
        List<Boolean> holdsLast = new ArrayList<>(many);
        holdsLast.set(299, true);

        assertEquals(StandingAtAPoint.AtTheRow.HOLDS, at(both, as(true), bs(holdsFirst)));
        assertEquals(StandingAtAPoint.AtTheRow.COULD_NOT_TELL, at(both, as(true), bs(holdsLast)));
        assertEquals(StandingAtAPoint.AtTheRow.COULD_NOT_TELL, at(both, as(true), bs(many)));
    }

    private static Proposition truthOf(TermPath one, TermPath other) {
        return Proposition.all(List.of(
                new Proposition.Truth(new DecisionSubject.AnInput(one), true),
                new Proposition.Truth(new DecisionSubject.AnInput(other), true)));
    }

    private static StandingAtAPoint.AtTheRow at(Proposition stated, ObservedValue xs,
                                                ObservedValue ys) {
        return at(stated, xs, ys, new ObservedValue.Sequence(List.of()));
    }

    private static StandingAtAPoint.AtTheRow at(Proposition stated, ObservedValue orders) {
        return at(stated, new ObservedValue.Sequence(List.of()),
                new ObservedValue.Sequence(List.of()), orders);
    }

    private static StandingAtAPoint.AtTheRow at(Proposition stated, ObservedValue xs,
                                                ObservedValue ys, ObservedValue orders) {
        BehaviorInputs where = new BehaviorInputs(List.of("xs", "ys", "orders"),
                List.of(new Type.ListOf(named("A")), new Type.ListOf(named("B")),
                        new Type.ListOf(named("Order"))),
                RuleReadings.ofSource(MODEL), POLICY);
        return StandingAtAPoint.atTheRow(stated, "decide", null, where,
                new ObservedInputs(List.of(xs, ys, orders), new Generator.Watched.NoAccount(),
                        new AnswerObservation.NotAnswered()), Set.of());
    }

    private static ObservedValue as(boolean... oks) {
        List<ObservedValue> out = new ArrayList<>();
        for (boolean ok : oks) {
            out.add(new ObservedValue.Constructed(sym("A"), Map.of("ok", new ObservedValue.Bool(ok))));
        }
        return new ObservedValue.Sequence(out);
    }

    private static ObservedValue bs(boolean... oks) {
        return new ObservedValue.Sequence(lines(oks));
    }

    private static ObservedValue bs(List<Boolean> oks) {
        boolean[] each = new boolean[oks.size()];
        for (int i = 0; i < each.length; i++) {
            each[i] = oks.get(i);
        }
        return bs(each);
    }

    private static List<ObservedValue> lines(boolean... oks) {
        List<ObservedValue> out = new ArrayList<>();
        for (boolean ok : oks) {
            out.add(new ObservedValue.Constructed(sym("B"), Map.of("ok", new ObservedValue.Bool(ok))));
        }
        return out;
    }

    private static ObservedValue order(boolean flag, boolean... lineOks) {
        return new ObservedValue.Constructed(sym("Order"), Map.of(
                "flag", new ObservedValue.Bool(flag),
                "lines", new ObservedValue.Sequence(lines(lineOks))));
    }

    private static ObservedValue orders(ObservedValue... each) {
        return new ObservedValue.Sequence(List.of(each));
    }

    private static Type named(String data) {
        return Type.ref(sym(data));
    }

    private static TypeSymbol sym(String data) {
        return TypeSymbols.declared(new TypeKey("g", data));
    }
}
