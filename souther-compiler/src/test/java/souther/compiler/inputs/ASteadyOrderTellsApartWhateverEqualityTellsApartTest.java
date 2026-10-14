package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Clause;
import souther.compiler.check.ClauseName;
import souther.compiler.check.PartId;
import souther.compiler.check.RuleRef;
import souther.compiler.diag.QuotedFrom;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.observe.Figure;
import souther.compiler.partition.ClassOfAPosition;
import souther.compiler.partition.ReportedReason;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.WrittenOwner;
import souther.compiler.values.StoppedReading;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A steady order calls two values one exactly where they are one.
 *
 * <p>What an order of this kind is for is that a reader comparing two runs over one source finds a
 * difference only where the model has one. An order that answers "the same" for values this
 * compiler tells apart does not do that: the two fall to whichever order a walk met them in, and a
 * document comes out one way on one run and the other way on the next.
 *
 * <p><b>So the contract is the one a sort needs, and it is checked rather than described.</b> Each
 * of these orders lists by hand what its values are made of, and nothing ties that list to the
 * components the values have: a component added to a record changes no switch, and javac has
 * nothing to refuse. So each order is asked over values read off its type ({@link ValuesOfAType}),
 * in which every component of every record it reaches is varied on its own, and a component added
 * later is varied without anybody adding an example.
 *
 * <p>What that does not make is two values that differ in two components at once, and a
 * comparison built out of a rendering — two names run together into one word — is wrong exactly
 * there. Nor a component left absent, which it never offers. Those pairs are written out below.
 */
class ASteadyOrderTellsApartWhateverEqualityTellsApartTest {

    private final ValuesOfAType values = new ValuesOfAType();

    @Test
    void aReasonARuleReadingStoppedFor() {
        assertEquals(List.of(), whereItIsNoOrder(
                BlockReason.RuleReadingStopped.IN_A_STEADY_ORDER,
                values.of(BlockReason.RuleReadingStopped.class)));
    }

    @Test
    void aSiteInARule() {
        assertEquals(List.of(), whereItIsNoOrder(RuleSite.IN_A_STEADY_ORDER,
                values.of(RuleSite.class)));
    }

    @Test
    void anOwnerOfAConstruct() {
        assertEquals(List.of(), whereItIsNoOrder(WrittenOwner.inASteadyOrder(),
                values.of(WrittenOwner.class)));
    }

    @Test
    void aConstructASourceWrote() {
        assertEquals(List.of(), whereItIsNoOrder(SourceConstructOrigin.inASteadyOrder(),
                values.of(SourceConstructOrigin.class)));
    }

    @Test
    void aTextAPositionIsQuotedFrom() {
        assertEquals(List.of(), whereItIsNoOrder(QuotedFrom.inASteadyOrder(),
                values.of(QuotedFrom.class)));
    }

    @Test
    void aModuleThatPublishedAText() {
        assertEquals(List.of(), whereItIsNoOrder(SourceProvenance.inASteadyOrder(),
                values.of(SourceProvenance.class)));
    }

    @Test
    void aReadingOfValuesThatStopped() {
        assertEquals(List.of(), whereItIsNoOrder(StoppedReading.IN_A_STEADY_ORDER,
                values.of(StoppedReading.class)));
    }

    @Test
    void aWordADocumentWritesForAStop() {
        assertEquals(List.of(), whereItIsNoOrder(ReportedReason.Stop.IN_A_STEADY_ORDER,
                values.of(ReportedReason.Stop.class)));
    }

    @Test
    void aClassOfAPositionEitherWay() {
        assertEquals(List.of(), whereItIsNoOrder(ClassOfAPosition.steadyOrder(),
                values.of(ClassOfAPosition.class)));
        assertEquals(List.of(), whereItIsNoOrder(ClassOfAPosition.byClassIdOrder(),
                values.of(ClassOfAPosition.class)));
    }

    /** A figure, one at a time, which is how a list of them is compared. */
    @Test
    void aFigureAWorkWasHeldTo() {
        Comparator<Figure> oneByOne = (one, other) -> Figure.compare(List.of(one), List.of(other));
        assertEquals(List.of(), whereItIsNoOrder(oneByOne, values.of(Figure.class)));
    }

    /**
     * And no two kinds of figure share a name.
     *
     * <p>The order compares a figure by its name and what it stood at, and the two kinds of figure
     * take their names from two vocabularies. A name in both would make a figure of one kind and
     * a figure of the other that stood at the same number, and the order would call them one.
     */
    @Test
    void aFigureIsNamedApartFromEveryFigureOfAnotherKind() {
        List<String> shared = new ArrayList<>();
        for (Object one : values.of(Figure.class)) {
            for (Object other : values.of(Figure.class)) {
                if (one.getClass() != other.getClass()
                        && ((Figure) one).name().equals(((Figure) other).name())) {
                    shared.add(one + " and " + other);
                }
            }
        }
        assertEquals(List.of(), shared);
    }

    /**
     * The check itself, against an order that leaves out one component.
     *
     * <p>Without this, an order nothing was asked of and an order that reads everything look alike.
     */
    @Test
    void anOrderThatLeavesOutAComponentIsCaught() {
        Comparator<Kept> byTheReasonAlone =
                Comparator.comparing(Kept::reason, StoppedReading.IN_A_STEADY_ORDER);
        assertFalse(whereItIsNoOrder(byTheReasonAlone, values.of(Kept.class)).isEmpty());
    }

    /** And a component nothing says how to make is refused rather than passed over. */
    @Test
    void aComponentNoValueOfCanBeMadeIsRefused() {
        assertThrows(AssertionError.class, () -> values.of(Unmade.class));
    }

    private record Kept(StoppedReading reason, boolean twice) {
    }

    private record Unmade(Thread runs) {
    }

    /** An owner by which module wrote it and what it names, never the two run together. */
    @Test
    void anOwnerIsToldApartByEachOfItsNames() {
        tellsApart(WrittenOwner.inASteadyOrder(),
                new WrittenOwner.Body("a b", "c"),
                new WrittenOwner.Body("a", "b c"));
    }

    /** And a construct by the owner that counted it, through that owner's own order. */
    @Test
    void aConstructIsToldApartByTheOwnerThatCountedIt() {
        tellsApart(SourceConstructOrigin.inASteadyOrder(),
                new SourceConstructOrigin(new WrittenOwner.Body("a b", "c"), 0, 0,
                        SourceConstruct.CALL),
                new SourceConstructOrigin(new WrittenOwner.Body("a", "b c"), 0, 0,
                        SourceConstruct.CALL));
    }

    /**
     * And a construct no source wrote from one a source did, which is the one origin whose owner
     * is absent.
     */
    @Test
    void anUnwrittenConstructIsToldFromAWrittenOne() {
        tellsApart(SourceConstructOrigin.inASteadyOrder(),
                SourceConstructOrigin.unwritten(),
                SourceConstructOrigin.written(new WrittenOwner.Body("a", "b"), 0,
                        SourceConstruct.CALL));
    }

    /** And a rule site by the declaration a part is of, module and name apart. */
    @Test
    void aRuleSiteIsToldApartByTheWholeOfWhatAPartIs() {
        tellsApart(RuleSite.IN_A_STEADY_ORDER,
                RuleSite.at(part("a b", "c")),
                RuleSite.at(part("a", "b c")));
    }

    /**
     * Where {@code order} is not an order over {@code these} that calls two of them one exactly
     * where they are one value: each pair it calls one and is not, or the other way round, each
     * pair it answers differently by which was handed over first, and each pair a sort by it leaves
     * out of order.
     *
     * <p>The last is what holds it to being an order at all. Two values compared either way round
     * agree, and every two of them in a list sorted by it come in that order, only where the order
     * is one sequence over all of them.
     */
    @SuppressWarnings("unchecked")
    private static <T> List<String> whereItIsNoOrder(Comparator<? super T> order,
                                                     List<Object> these) {
        List<T> all = (List<T>) these;
        List<String> out = new ArrayList<>();
        for (T one : all) {
            for (T other : all) {
                int either = order.compare(one, other);
                if ((either == 0) != one.equals(other)) {
                    out.add((either == 0 ? "called one: " : "called two: ") + one + " and "
                            + other);
                }
                if (Integer.signum(either) != -Integer.signum(order.compare(other, one))) {
                    out.add("answered by which came first: " + one + " and " + other);
                }
            }
        }
        if (!out.isEmpty()) {
            return out;
        }
        List<T> sorted = new ArrayList<>(all);
        sorted.sort(order);
        for (int i = 0; i < sorted.size(); i++) {
            for (int j = i + 1; j < sorted.size(); j++) {
                if (order.compare(sorted.get(i), sorted.get(j)) >= 0) {
                    out.add("sorted out of order: " + sorted.get(i) + " before " + sorted.get(j));
                }
            }
        }
        return out;
    }

    /**
     * Two values this compiler tells apart are told apart by {@code order}, both ways round.
     *
     * <p>Both ways because a comparison is two claims: that neither is the same as the other, and
     * that which of them comes first does not turn on which was handed over first.
     */
    private static <T> void tellsApart(Comparator<T> order, T one, T other) {
        assertNotEquals(one, other, "this measures an order over values that are not one value");
        assertNotEquals(0, order.compare(one, other),
                "these are two values, and an order calling them one leaves them wherever the walk"
                        + " put them: " + one + " and " + other);
        assertEquals(Math.signum(order.compare(one, other)),
                -Math.signum(order.compare(other, one)),
                "and which of them comes first is the same question asked either way round");
    }

    private static PartId<RuleRef.Invariant> part(String module, String declared) {
        return new PartId<>(new RuleRef.Invariant(new Clause.Ref(
                new Clause.Id(TypeSymbols.declared(new TypeKey(module, declared)), 0),
                Optional.<ClauseName>empty())), 0);
    }
}
