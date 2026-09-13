package souther.compiler.examples;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.CheckedDeclarations;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.observe.Alignment;
import souther.compiler.observe.Asserted;
import souther.compiler.observe.Comparisons;
import souther.compiler.observe.FieldTypes;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.Position;
import souther.compiler.observe.ValueTypes;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value with no order is written in one, and it is neither side's.
 *
 * <p>A map and a set state no order, and what came out of a run holds its parts where a table put
 * them — a fact about the numbers they hashed to. Neither does the row beside it have one to lend: a
 * row states a value rather than the way its source built one, what it wrote is run, and what comes
 * back went through a table too. So both look like somebody's sequence and neither is.
 *
 * <p><b>Showing a value as a sequence is the report's doing, so the report is what supplies the
 * order.</b> Both sides are written in one this compiler settles on. Nothing about the values
 * changes: a map is no more ordered for having been written out, and nothing may read the sequence
 * as a fact about it.
 *
 * <p><b>Which of the answer's parts goes with which of the row's is still the comparison's
 * answer.</b> Each takes the place its counterpart takes, so two that are one value stand together
 * even where they are spelled apart. A part with no counterpart follows the ones that have them.
 */
class AnUnorderedValueIsWrittenInOneOrderTest {

    private static final Type OF_TEXT = Type.map(Type.STRING);
    private static final Type OF_DECIMAL = Type.map(Type.DECIMAL, Type.STRING);
    private static final Type OF_MAPS = Type.map(Type.STRING, Type.map(Type.STRING));
    private static final Type SET_OF_MAPS = Type.set(Type.map(Type.STRING));
    private static final Type OF_SETS = Type.map(Type.STRING, Type.set(Type.STRING));

    private static ValueRendering rendering() {
        Symbols symbols = Symbols.none(DefaultStdlib.get());
        return new ValueRendering(new NeutralForm(symbols, ScopedDeclarations.of(symbols),
                ScopedDeclarations.kindsOf(symbols),
                FieldTypes.over(new CheckedDeclarations(_ -> null, _ -> null))));
    }

    private static ValueTypes types() {
        return ValueTypes.over(FieldTypes.over(new CheckedDeclarations(_ -> null, _ -> null)));
    }

    /** What a reader is shown of {@code answered}, beside a row that stated {@code wrote}. */
    private static String shown(ObservedValue answered, Asserted wrote, Type position) {
        Alignment alignment =
                Comparisons.alignment(wrote, answered, types(), Position.at(position));
        return rendering().show(answered, position, alignment);
    }

    private static ObservedValue text(String s) {
        return new ObservedValue.Text(s);
    }

    private static ObservedValue.Mapping answered(String... keys) {
        List<ObservedValue.Entry> out = new ArrayList<>();
        for (String key : keys) {
            out.add(new ObservedValue.Entry(text(key), text(key + "!")));
        }
        return new ObservedValue.Mapping(out);
    }

    private static Asserted.Entry entry(BigDecimal key, String value) {
        return new Asserted.Entry(new Asserted.Value(new ObservedValue.Decimal(key)),
                new Asserted.Value(text(value)));
    }

    private static ObservedValue.Entry pair(BigDecimal key, String value) {
        return new ObservedValue.Entry(new ObservedValue.Decimal(key), text(value));
    }

    private static Asserted wrote(String... keys) {
        List<Asserted.Entry> out = new ArrayList<>();
        for (String key : keys) {
            out.add(new Asserted.Entry(new Asserted.Value(text(key)),
                    new Asserted.Value(text(key + "!"))));
        }
        return new Asserted.Entries(false, out);
    }

    /**
     * The control. Two answers holding their pairs alike would be written out alike by a rendering
     * that decides nothing, and everything below would hold of that one too.
     *
     * <p>Said of what the values hold rather than of what they are written as, because what they are
     * written as is the thing under test.
     */
    @Test
    void theTwoAnswersDoNotHoldTheirPairsAlike() {
        Set<List<String>> held = new LinkedHashSet<>();
        for (ObservedValue.Mapping each : List.of(answered("b", "a"), answered("a", "b"))) {
            List<String> keys = new ArrayList<>();
            each.entries().forEach(pair -> keys.add(((ObservedValue.Text) pair.key()).value()));
            held.add(keys);
        }

        assertTrue(held.size() > 1,
                () -> "the two answers hold their pairs in one order, so nothing below turns on"
                        + " which order a value came out holding: " + held);
    }

    /**
     * One order, and neither side's.
     *
     * <p>A row states a value and not the way its source happened to build one, so the map it states
     * holds its pairs in whatever a table walked — the same kind of accident the answer's own order
     * is. Following either of them puts one accident where the other was.
     */
    @Test
    void thePairsComeInOneOrderThatIsNeitherSidesOwn() {
        assertEquals("[ (\"a\", \"a!\"), (\"b\", \"b!\") ]",
                shown(answered("a", "b"), wrote("b", "a"), OF_TEXT));
    }

    /** However the answer holds them. */
    @Test
    void theOrderTheAnswerHoldsThemInDecidesNothing() {
        assertEquals(shown(answered("a", "b"), wrote("b", "a"), OF_TEXT),
                shown(answered("b", "a"), wrote("b", "a"), OF_TEXT));
    }

    /**
     * A key the row wrote another way is still the key the row wrote.
     *
     * <p>A decimal is the amount it stands for, so {@code 1.0} and {@code 1.00} are one key and the
     * comparison pairs them. Found again from what the two are written as, they are two, and the
     * answer's pair would be shown as one no row mentions — with the row's own pair nowhere.
     */
    @Test
    void aKeyWrittenTwoWaysIsOneKey() {
        // The key written two ways is written first, and two more follow it, so that failing to
        // find it is not written the same as finding it: unplaced pairs go after the placed ones.
        Asserted row = new Asserted.Entries(false, List.of(
                entry(new BigDecimal("1.0"), "one"),
                entry(new BigDecimal("2"), "two"),
                entry(new BigDecimal("3"), "three")));
        ObservedValue answer = new ObservedValue.Mapping(List.of(
                pair(new BigDecimal("3"), "three"),
                pair(new BigDecimal("1.00"), "one"),
                pair(new BigDecimal("2"), "two")));

        assertEquals("[ (1.00, \"one\"), (2, \"two\"), (3, \"three\") ]",
                shown(answer, row, OF_DECIMAL));
    }

    /**
     * A set is shown the way a map is: each element at the place its counterpart takes.
     *
     * <p>A set holds no order of its own either, so which element of the answer stands in a place is
     * a fact about what its elements hashed to. Which of the row's each stands for is the
     * comparison's answer — paired by where they stand instead, the map inside one element would be
     * put in the order of a map inside another, and the report would write an answer in the shape of
     * a value it is not about.
     */
    @Test
    void anElementOfASetIsReadAgainstTheOneItStandsFor() {
        // Each row element writes its pairs the other way round from the alphabet, so that being
        // paired with the wrong one is not written the same as being paired with the right one:
        // a map nothing states is written out in order, which is what the alphabet would give.
        Asserted row = new Asserted.Elements(Asserted.Container.SET, List.of(
                wrote("y", "x"), wrote("q", "p")));
        ObservedValue answer = new ObservedValue.Sequence(List.of(
                answered("p", "q"), answered("x", "y")));

        assertEquals("Set.fromList([ [ (\"p\", \"p!\"), (\"q\", \"q!\") ],"
                        + " [ (\"x\", \"x!\"), (\"y\", \"y!\") ] ])",
                shown(answer, row, SET_OF_MAPS));
    }

    /**
     * A pair the row did not write follows the ones it did, all the way down.
     *
     * <p>Nothing of the author's says where it goes, so it is written in the one form two runs of it
     * agree on — and a map it holds of its own is in that form too. Left as the run's table walked
     * it, the number is back in the report one level below where it was taken out.
     */
    @Test
    void aPairTheRowDidNotWriteIsWrittenTheOneWayAllTheWayDown() {
        Asserted row = new Asserted.Entries(false, List.of(
                new Asserted.Entry(new Asserted.Value(text("kept")), wrote("a", "b"))));
        ObservedValue answer = new ObservedValue.Mapping(List.of(
                new ObservedValue.Entry(text("extra"), answered("z", "y")),
                new ObservedValue.Entry(text("kept"), answered("b", "a"))));

        assertEquals("[ (\"kept\", [ (\"a\", \"a!\"), (\"b\", \"b!\") ]),"
                        + " (\"extra\", [ (\"y\", \"y!\"), (\"z\", \"z!\") ]) ]",
                shown(answer, row, OF_MAPS));
    }

    /**
     * A set under a pair the row did not write is written the one way too.
     *
     * <p>The pair has no place of the author's, so it is written in the form two runs agree on — and
     * a set it holds is a collection with no order of its own, which the declaration is the only
     * thing that says. Written out as the run's table walked it, the number the elements hashed to
     * is back in the report one level below where it was taken out.
     */
    @Test
    void aSetUnderAPairNobodyWroteIsWrittenTheOneWay() {
        Asserted row = new Asserted.Entries(false, List.of(
                new Asserted.Entry(new Asserted.Value(text("kept")), wrote("a", "b"))));

        assertEquals(shown(withExtraSet("z", "a"), row, OF_SETS),
                shown(withExtraSet("a", "z"), row, OF_SETS));
    }

    /** A map holding the pair the row wrote and one it did not, whose value is a set. */
    private static ObservedValue withExtraSet(String... elements) {
        List<ObservedValue> held = new ArrayList<>();
        for (String each : elements) {
            held.add(text(each));
        }
        return new ObservedValue.Mapping(List.of(
                new ObservedValue.Entry(text("extra"), new ObservedValue.Sequence(held)),
                new ObservedValue.Entry(text("kept"), new ObservedValue.Sequence(List.of()))));
    }

    /** And with no row read against it, the answer is written in that order all the same: what puts
     *  a map's pairs somewhere is the report, and a row beside it changes nothing about that. */
    @Test
    void withNothingWrittenBesideItTheAnswerIsShownInTheSameOrder() {
        assertEquals("[ (\"a\", \"a!\"), (\"b\", \"b!\") ]",
                rendering().show(answered("b", "a"), OF_TEXT));
    }
}
