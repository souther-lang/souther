package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Symbols;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.math.BigDecimal;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The equality two structured values are compared by.
 *
 * <p>What a row asserted and what a behavior answered are held against each other here, and the
 * corpus does not settle the rules: a set and a list are read back as the same kind of value, an
 * empty one carries almost nothing, and two decimals that differ in scale are one amount. So each is
 * fixed here rather than inferred from rows that happen to pass.
 *
 * <p>The position is semantic context. It says whether order is part of being the same value, and it
 * never supplies a name: the {@code List} and {@code Set} readings of one pair of sequences differ,
 * and neither turns a value into one of another type.
 */
class ValueMatchTest {

    private static ValueMatch match() {
        Symbols symbols = Symbols.none();
        NeutralForm neutral = new NeutralForm(symbols);
        return new ValueMatch(neutral, new ValueRendering(neutral));
    }

    /** A value with no parts, on either side. */
    private static ObservedValue n(long v) {
        return new ObservedValue.Integer(v);
    }

    private static Asserted said(ObservedValue v) {
        return new Asserted.Value(v);
    }

    /** What a row wrote without saying which collection it is: `[ … ]`. */
    private static Asserted wrote(ObservedValue... elements) {
        List<Asserted> out = new java.util.ArrayList<>();
        for (ObservedValue e : elements) {
            out.add(said(e));
        }
        return new Asserted.Elements(Asserted.Container.UNSTATED, out);
    }

    /** What a row wrote saying it: `Set.fromList([ … ])`. */
    private static Asserted wroteASet(ObservedValue... elements) {
        List<Asserted> out = new java.util.ArrayList<>();
        for (ObservedValue e : elements) {
            out.add(said(e));
        }
        return new Asserted.Elements(Asserted.Container.SET, out);
    }

    private static ObservedValue seq(ObservedValue... elements) {
        return new ObservedValue.Sequence(List.of(elements));
    }

    private static final Type INT = Type.Prim.named("Int");
    private static final Type LIST = Type.list(INT);
    private static final Type SET = Type.set(INT);
    private static final Type MAP = Type.map(INT, INT);

    private static void holds(Asserted a, ObservedValue b, Type position) {
        assertNull(match().compare(a, b, position), "the two state the same value");
    }

    private static void holds(ObservedValue a, ObservedValue b, Type position) {
        holds(said(a), b, position);
    }

    private static ValueMatch.Mismatch differs(Asserted a, ObservedValue b, Type position) {
        ValueMatch.Mismatch m = match().compare(a, b, position);
        assertNotNull(m, "the two state different values");
        return m;
    }

    private static ValueMatch.Mismatch differs(ObservedValue a, ObservedValue b, Type position) {
        return differs(said(a), b, position);
    }

    @Test
    void aListIsItsElementsInOrder() {
        holds(wrote(n(1), n(2)), seq(n(1), n(2)), LIST);
        assertEquals(ValueMatch.Reason.VALUE, differs(wrote(n(1), n(2)), seq(n(2), n(1)), LIST).reason());
        assertEquals("$[0]", differs(wrote(n(1), n(2)), seq(n(2), n(1)), LIST).path());
    }

    @Test
    void aSetIsItsElements() {
        holds(wrote(n(1), n(2)), seq(n(1), n(2)), SET);
        holds(wrote(n(1), n(2)), seq(n(2), n(1)), SET);
        assertEquals(ValueMatch.Reason.SHAPE, differs(wrote(n(1), n(2)), seq(n(1), n(3)), SET).reason());
    }

    @Test
    void aRowThatSaidNothingAboutWhichCollectionIsReadAtTheAnswers() {
        // `[ 1, 2 ]` is how a list and a set are both written, so it states no preference and the
        // answer's own type says which reading applies. The one pair, read both ways, answers
        // differently — a comparison that lost that would give one answer for both.
        holds(wrote(n(1), n(2)), seq(n(2), n(1)), SET);
        assertNotNull(match().compare(wrote(n(1), n(2)), seq(n(2), n(1)), LIST),
                "a list is its elements in order, whatever a set of the same elements is");
    }

    @Test
    void aRowThatSaidWhichCollectionItWroteIsHeldToIt() {
        // And the other way. `Set.fromList([ 1 ])` states a set wherever it stands, so a behavior
        // answering with a list did not answer with it — which the position must not be allowed to
        // paper over, since it is the answer's type and not the row's.
        holds(wroteASet(n(1), n(2)), seq(n(1), n(2)), SET);
        assertEquals(ValueMatch.Reason.TYPE, differs(wroteASet(n(1)), seq(n(1)), LIST).reason());
        // An empty one carries nothing at all, so it is only what the row said that tells them apart.
        assertEquals(ValueMatch.Reason.TYPE, differs(wroteASet(), seq(), LIST).reason());
        holds(wroteASet(), seq(), SET);
    }

    @Test
    void aSequenceAndAMapAreNeverOneValue() {
        assertEquals(ValueMatch.Reason.TYPE,
                differs(new Asserted.Entries(true, List.of()), seq(), MAP).reason());
        assertEquals(ValueMatch.Reason.TYPE,
                differs(wroteASet(), new ObservedValue.Mapping(List.of()), MAP).reason());
    }

    @Test
    void anEmptyCollectionIsStillReadAtItsPosition() {
        holds(wrote(), seq(), LIST);
        holds(wrote(), seq(), SET);
        holds(new Asserted.Entries(false, List.of()), new ObservedValue.Mapping(List.of()), MAP);
        // An empty sequence and an empty map carry the same nothing, and are not the same value.
        assertEquals(ValueMatch.Reason.TYPE,
                differs(wrote(), new ObservedValue.Mapping(List.of()), MAP).reason());
    }

    @Test
    void aMapIsMatchedByKeyRatherThanLookedUpByOne() {
        Asserted a = new Asserted.Entries(false, List.of(
                new Asserted.Entry(said(n(1)), said(new ObservedValue.Text("a"))),
                new Asserted.Entry(said(n(2)), said(new ObservedValue.Text("b")))));
        ObservedValue.Mapping reversed = new ObservedValue.Mapping(List.of(
                new ObservedValue.Entry(n(2), new ObservedValue.Text("b")),
                new ObservedValue.Entry(n(1), new ObservedValue.Text("a"))));
        holds(a, reversed, Type.map(INT, Type.Prim.named("String")));

        ObservedValue.Mapping wrongValue = new ObservedValue.Mapping(List.of(
                new ObservedValue.Entry(n(1), new ObservedValue.Text("a")),
                new ObservedValue.Entry(n(2), new ObservedValue.Text("z"))));
        ValueMatch.Mismatch m = differs(a, wrongValue, Type.map(INT, Type.Prim.named("String")));
        assertEquals(ValueMatch.Reason.VALUE, m.reason());
        assertEquals("$[2]", m.path(), "the entry is named by its key, not by where it was written");
    }

    @Test
    void aDecimalIsTheAmountItStandsFor() {
        // What `Values.equal` says of the run-time values: two that differ only in scale are one amount.
        holds(new ObservedValue.Decimal(new BigDecimal("1.0")),
                new ObservedValue.Decimal(new BigDecimal("1.00")), Type.Prim.named("Decimal"));
        assertEquals(ValueMatch.Reason.VALUE,
                differs(new ObservedValue.Decimal(new BigDecimal("1.0")),
                        new ObservedValue.Decimal(new BigDecimal("1.5")),
                        Type.Prim.named("Decimal")).reason());
    }

    @Test
    void aDecimalKeyIsMatchedByTheAmountToo() {
        Asserted a = new Asserted.Entries(false, List.of(
                new Asserted.Entry(said(new ObservedValue.Decimal(new BigDecimal("1.0"))), said(n(7)))));
        ObservedValue.Mapping b = new ObservedValue.Mapping(List.of(
                new ObservedValue.Entry(new ObservedValue.Decimal(new BigDecimal("1.00")), n(7))));
        holds(a, b, Type.map(Type.Prim.named("Decimal"), INT));
    }

    @Test
    void aValueUnderANameIsNotTheBaseItWraps() {
        // The whole of #653, at the level the comparison works at: one representation, two types.
        TypeName amount = new TypeName("demo", "AmountN");
        ObservedValue wrapped = new ObservedValue.Constructed(amount,
                java.util.Map.of("value", n(1)));
        ValueMatch.Mismatch m = differs(said(n(1)), wrapped, Type.ref(amount));
        assertEquals(ValueMatch.Reason.TYPE, m.reason());
    }

    @Test
    void twoNamesOverOneBaseAreTwoTypes() {
        Asserted one = new Asserted.Built(new TypeName("demo", "AmountN"),
                java.util.Map.of("value", said(n(1))));
        ObservedValue other = new ObservedValue.Constructed(new TypeName("demo", "OtherAmountN"),
                java.util.Map.of("value", n(1)));
        assertEquals(ValueMatch.Reason.TYPE, differs(one, other, null).reason());
    }

    @Test
    void aDateIsNotTheTextThatSpellsIt() {
        assertEquals(ValueMatch.Reason.TYPE,
                differs(new ObservedValue.Text("2026-07-25"),
                        new ObservedValue.Temporal("2026-07-25"), Type.Prim.named("Date")).reason());
    }

    @Test
    void anAbsentValueIsNotAPresentOne() {
        assertEquals(ValueMatch.Reason.ABSENCE,
                differs(new ObservedValue.Absent(), n(1), Type.option(INT)).reason());
        holds(new ObservedValue.Absent(), new ObservedValue.Absent(), Type.option(INT));
    }

    @Test
    void aValueThatCouldNotBeReadIsNotAValueThatMatches() {
        assertEquals(ValueMatch.Reason.UNREADABLE,
                differs(new ObservedValue.Unknown("why"), n(1), INT).reason());
        assertEquals(ValueMatch.Reason.UNREADABLE,
                differs(n(1), new ObservedValue.Truncated(), INT).reason());
    }

    @Test
    void twoValuesTheObservationStoppedAreNotOneValue() {
        // Both sides stopping at the same limit is the limit being reached twice, and says nothing
        // about what stood past it. Reading it as equality is how a depth bound answers "the same"
        // for two values that differ only below it.
        assertEquals(ValueMatch.Reason.UNREADABLE,
                differs(new ObservedValue.Truncated(), new ObservedValue.Truncated(), INT).reason());
        assertEquals(ValueMatch.Reason.UNREADABLE,
                differs(new ObservedValue.Unknown("a"), new ObservedValue.Unknown("a"), INT).reason());
    }

    @Test
    void aValueDeeperThanTheComparisonReadsIsStoppedRatherThanFlattened() {
        // The limit a comparison observes under is wide, not absent. What is past it has to arrive as
        // something the comparison refuses to call equal, which the case above fixes.
        Object deep = 1L;
        for (int i = 0; i < FixtureReader.WHOLE.maxDepth() + 2; i++) {
            deep = List.of(deep);
        }
        Symbols symbols = Symbols.none();
        ObservedValue observed = ObservedValues.of(deep, symbols, new NeutralForm(symbols),
                FixtureReader.WHOLE);
        ObservedValue at = observed;
        while (at instanceof ObservedValue.Sequence s) {
            at = s.elements().get(0);
        }
        assertEquals(new ObservedValue.Truncated(), at, "the walk stops rather than reading on");
    }
}
