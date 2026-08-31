package souther.compiler.observe;

import org.junit.jupiter.api.Test;

import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.math.BigDecimal;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The equality two structured values are compared by.
 *
 * <p>What was stated and what was answered are held against each other here, and the corpus does not
 * settle the rules: a set and a list are read back as the same kind of value, an empty one carries
 * almost nothing, and two decimals that differ in scale are one amount. So each is fixed here rather
 * than inferred from rows that happen to pass.
 *
 * <p>The position is semantic context. It says whether order is part of being the same value, and it
 * never supplies a name: the {@code List} and {@code Set} readings of one pair of sequences differ,
 * and neither turns a value into one of another type.
 *
 * <p>What it reads of the declarations is one question, so this is written with an answer to that
 * question and nothing else — no module, no compiler, no reading of a source.
 */
class ValueMatchTest {

    private static final TypeSymbol.AtModule RECEIPT =
            TypeSymbols.declared(new TypeKey("demo", "Receipt"));

    /** What a declaration would say, written out: `Receipt.lines` is a set of ints and nothing else
     *  is declared anywhere. */
    private static final ValueTypes TYPES = ValueTypes.over(owner ->
            RECEIPT.equals(owner) ? java.util.Map.of("lines", Type.set(Type.Prim.named("Int")))
                    : java.util.Map.of());

    private static ValueMatch match() {
        return new ValueMatch(TYPES);
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
        assertNull(match().compare(a, b, at(position)), "the two state the same value");
    }

    private static void holds(ObservedValue a, ObservedValue b, Type position) {
        holds(said(a), b, position);
    }

    private static Mismatch differs(Asserted a, ObservedValue b, Type position) {
        Mismatch m = match().compare(a, b, at(position));
        assertNotNull(m, "the two state different values");
        return m;
    }

    private static Mismatch differs(ObservedValue a, ObservedValue b, Type position) {
        return differs(said(a), b, position);
    }

    private static Position at(Type position) {
        return position == null ? Position.UNREAD : Position.at(position);
    }

    /**
     * What a text stated cannot be changed after it was read.
     *
     * <p>What this is compared against is what was written down once, and a value whose parts could
     * be reached into is one whose answer moves after it was compared — by whoever built it, or by
     * whoever it was handed to.
     */
    @Test
    void whatWasStatedIsNotChangedByWhoeverHoldsIt() {
        List<Asserted> given = new java.util.ArrayList<>();
        given.add(said(n(1)));
        Asserted.Elements stated = new Asserted.Elements(Asserted.Container.LIST, given);
        given.add(said(n(2)));
        assertEquals(1, stated.elements().size(), "a list handed over is copied");

        java.util.Map<String, Asserted> fields = new java.util.LinkedHashMap<>();
        fields.put("lines", said(n(1)));
        Asserted.Built built = new Asserted.Built(RECEIPT, fields);
        fields.put("other", said(n(2)));
        assertEquals(java.util.Set.of("lines"), built.fields().keySet(),
                "and so is a construction's parts");
    }

    @Test
    void aListIsItsElementsInOrder() {
        holds(wrote(n(1), n(2)), seq(n(1), n(2)), LIST);
        assertEquals(Mismatch.Reason.VALUE, differs(wrote(n(1), n(2)), seq(n(2), n(1)), LIST).reason());
        assertEquals(List.of(new PathElement.Index(0)),
                differs(wrote(n(1), n(2)), seq(n(2), n(1)), LIST).path());
    }

    @Test
    void aSetIsItsElements() {
        holds(wrote(n(1), n(2)), seq(n(1), n(2)), SET);
        holds(wrote(n(1), n(2)), seq(n(2), n(1)), SET);
        assertEquals(Mismatch.Reason.SHAPE, differs(wrote(n(1), n(2)), seq(n(1), n(3)), SET).reason());
    }

    @Test
    void aRowThatSaidNothingAboutWhichCollectionIsReadAtTheAnswers() {
        // `[ 1, 2 ]` is how a list and a set are both written, so it states no preference and the
        // answer's own type says which reading applies. The one pair, read both ways, answers
        // differently — a comparison that lost that would give one answer for both.
        holds(wrote(n(1), n(2)), seq(n(2), n(1)), SET);
        assertNotNull(match().compare(wrote(n(1), n(2)), seq(n(2), n(1)), at(LIST)),
                "a list is its elements in order, whatever a set of the same elements is");
    }

    @Test
    void aRowThatSaidWhichCollectionItWroteIsHeldToIt() {
        // And the other way. `Set.fromList([ 1 ])` states a set wherever it stands, so a behavior
        // answering with a list did not answer with it — which the position must not be allowed to
        // paper over, since it is the answer's type and not the row's.
        holds(wroteASet(n(1), n(2)), seq(n(1), n(2)), SET);
        assertEquals(Mismatch.Reason.TYPE, differs(wroteASet(n(1)), seq(n(1)), LIST).reason());
        // An empty one carries nothing at all, so it is only what the row said that tells them apart.
        assertEquals(Mismatch.Reason.TYPE, differs(wroteASet(), seq(), LIST).reason());
        holds(wroteASet(), seq(), SET);
    }

    /**
     * And what says which collection a field holds is what declares that field.
     *
     * <p>The one thing a comparison cannot read off either value. Asked of the declarations, the
     * elements of {@code lines} are a set and their order is not part of the value; asked of
     * nothing, they are read in the order they stand.
     */
    @Test
    void andWhatAFieldHoldsIsWhatItsDeclarationSays() {
        Asserted stated = new Asserted.Built(RECEIPT,
                java.util.Map.of("lines", wrote(n(1), n(2))));
        ObservedValue answered = new ObservedValue.Constructed(RECEIPT,
                java.util.Map.of("lines", seq(n(2), n(1))));
        assertNull(match().compare(stated, answered, Position.UNREAD),
                "the field is declared a set, so the order it stands in is not part of it");

        ValueMatch nothingDeclared = new ValueMatch(ValueTypes.over(owner -> java.util.Map.of()));
        Mismatch differs = nothingDeclared.compare(stated, answered, Position.UNREAD);
        assertNotNull(differs, "with nothing declaring the field, the elements are read in order");
        assertEquals(List.of(new PathElement.Field("lines"), new PathElement.Index(0)),
                differs.path());
    }

    @Test
    void aSequenceAndAMapAreNeverOneValue() {
        assertEquals(Mismatch.Reason.TYPE,
                differs(new Asserted.Entries(true, List.of()), seq(), MAP).reason());
        assertEquals(Mismatch.Reason.TYPE,
                differs(wroteASet(), new ObservedValue.Mapping(List.of()), MAP).reason());
    }

    @Test
    void anEmptyCollectionIsStillReadAtItsPosition() {
        holds(wrote(), seq(), LIST);
        holds(wrote(), seq(), SET);
        holds(new Asserted.Entries(false, List.of()), new ObservedValue.Mapping(List.of()), MAP);
        // An empty sequence and an empty map carry the same nothing, and are not the same value.
        assertEquals(Mismatch.Reason.TYPE,
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
        Mismatch m = differs(a, wrongValue, Type.map(INT, Type.Prim.named("String")));
        assertEquals(Mismatch.Reason.VALUE, m.reason());
        assertEquals(List.of(new PathElement.Key(said(n(2)))), m.path(),
                "the entry is named by its key, not by where it was written");
    }

    @Test
    void aDecimalIsTheAmountItStandsFor() {
        // What `Values.equal` says of the run-time values: two that differ only in scale are one amount.
        holds(new ObservedValue.Decimal(new BigDecimal("1.0")),
                new ObservedValue.Decimal(new BigDecimal("1.00")), Type.Prim.named("Decimal"));
        assertEquals(Mismatch.Reason.VALUE,
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
        // One representation, two types, at the level the comparison works at.
        TypeSymbol.AtModule amount = TypeSymbols.declared(new TypeKey("demo", "AmountN"));
        ObservedValue wrapped = new ObservedValue.Constructed(amount,
                java.util.Map.of("value", n(1)));
        Mismatch m = differs(said(n(1)), wrapped, Type.ref(amount));
        assertEquals(Mismatch.Reason.TYPE, m.reason());
    }

    @Test
    void twoNamesOverOneBaseAreTwoTypes() {
        Asserted one = new Asserted.Built(TypeSymbols.declared(new TypeKey("demo", "AmountN")),
                java.util.Map.of("value", said(n(1))));
        ObservedValue other = new ObservedValue.Constructed(TypeSymbols.declared(new TypeKey("demo", "OtherAmountN")),
                java.util.Map.of("value", n(1)));
        assertEquals(Mismatch.Reason.TYPE, differs(one, other, null).reason());
    }

    @Test
    void aDateIsNotTheTextThatSpellsIt() {
        assertEquals(Mismatch.Reason.TYPE,
                differs(new ObservedValue.Text("2026-07-25"),
                        new ObservedValue.Temporal("2026-07-25"), Type.Prim.named("Date")).reason());
    }

    @Test
    void anAbsentValueIsNotAPresentOne() {
        assertEquals(Mismatch.Reason.ABSENCE,
                differs(new ObservedValue.Absent(), n(1), Type.option(INT)).reason());
        holds(new ObservedValue.Absent(), new ObservedValue.Absent(), Type.option(INT));
    }

    @Test
    void aValueThatCouldNotBeReadIsNotAValueThatMatches() {
        assertEquals(Mismatch.Reason.UNREADABLE,
                differs(new ObservedValue.Unknown("why"), n(1), INT).reason());
        assertEquals(Mismatch.Reason.UNREADABLE,
                differs(n(1), new ObservedValue.Truncated(), INT).reason());
    }

    @Test
    void twoValuesTheObservationStoppedAreNotOneValue() {
        // Both sides stopping at the same limit is the limit being reached twice, and says nothing
        // about what stood past it. Reading it as equality is how a depth bound answers "the same"
        // for two values that differ only below it.
        assertEquals(Mismatch.Reason.UNREADABLE,
                differs(new ObservedValue.Truncated(), new ObservedValue.Truncated(), INT).reason());
        assertEquals(Mismatch.Reason.UNREADABLE,
                differs(new ObservedValue.Unknown("a"), new ObservedValue.Unknown("a"), INT).reason());
    }
}
