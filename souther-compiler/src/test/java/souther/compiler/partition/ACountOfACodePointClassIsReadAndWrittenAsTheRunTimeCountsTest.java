package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.types.Type;
import souther.compiler.values.AsACompilationAllows;

import java.util.ArrayList;
import java.util.List;
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many code points of a string are in a class is a number of its own at the string's position,
 * and the two directions of it — reading a row, writing a value — are held to each other and to
 * the run time's own whitespace.
 *
 * <p>The oracle is written here, in the strings themselves, and not read from the class that
 * counts: a reader and a writer that both counted by the same wrong alphabet agree with each other
 * at every string either offers.
 */
class ACountOfACodePointClassIsReadAndWrittenAsTheRunTimeCountsTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());
    private static final RuleReadingSource RULES = RuleReadings.ofNoClauseFiled(SYMBOLS);
    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12,
            AsACompilationAllows.admittedValues(), AsACompilationAllows.whatARuleLeaves());
    private static final RuleReadingContext READING = RuleReadingContext.unshared(RULES, POLICY);
    private static final NewtypeInners INNERS = ScopedDeclarations.wrapsOf(SYMBOLS);
    private static final TermPath AT = TermPath.of("t");

    private static final CodePointClass NOT_WHITESPACE = new CodePointClass.NotWhitespace();
    private static final CodePointClass NOT_WHITESPACE_NOR_COMMA =
            new CodePointClass.NotWhitespaceNorEqualTo(',');

    private static NumericTerm.CodePointClassCount counting(CodePointClass counted) {
        NumericTerm.CodePointClassCount made =
                NumericTerm.CodePointClassCount.of(AT, counted, Type.STRING, INNERS);
        assertNotNull(made, "a string's code points are counted");
        return made;
    }

    private static TermOrders ordersOf(CodePointClass counted) {
        return TermOrdersFixtures.at(counting(counted), Type.STRING, SYMBOLS);
    }

    /** Only a string has code points to count. */
    @Test
    void onlyAStringHasCodePointsToCount() {
        assertNull(NumericTerm.CodePointClassCount.of(AT, NOT_WHITESPACE, Type.INT, INNERS));
        assertNull(NumericTerm.CodePointClassCount.of(AT, NOT_WHITESPACE,
                new Type.ListOf(Type.STRING), INNERS));
    }

    /** Two counts are one term where the place and the class are, and two where either is not. */
    @Test
    void aCountIsNamedByThePlaceAndTheClass() {
        assertEquals(counting(NOT_WHITESPACE), counting(new CodePointClass.NotWhitespace()));
        assertNotEquals(counting(NOT_WHITESPACE), counting(NOT_WHITESPACE_NOR_COMMA));
        assertNotEquals(counting(NOT_WHITESPACE_NOR_COMMA),
                counting(new CodePointClass.NotWhitespaceNorEqualTo(';')));
        UnaryOperator<TermPath> there = path -> path.then("name");
        assertEquals(TermPath.of("t").then("name"),
                counting(NOT_WHITESPACE).movedTo(there).position());
        assertEquals(counting(NOT_WHITESPACE_NOR_COMMA).counted(),
                counting(NOT_WHITESPACE_NOR_COMMA).movedTo(there).counted());
    }

    /** Never below nought, and in whole numbers whatever the string is counted by. */
    @Test
    void aCountIsAWholeNumberFromNought() {
        NumericTerm.CodePointClassCount count = counting(NOT_WHITESPACE);
        assertTrue(count.intrinsicBounds().admits(Count.of(0)));
        assertTrue(!count.intrinsicBounds().admits(Count.of(-1)));
        assertEquals(Carrier.WHOLE, ordersOf(NOT_WHITESPACE).answered());
        assertEquals(Carrier.TEXT, ordersOf(NOT_WHITESPACE).observed());
    }

    /**
     * What each class counts in strings chosen to tell it from a plausible neighbour: the
     * whitespace the library trims and splits words on is the one Unicode alphabet, so an
     * ideographic space and a no-break space are whitespace and a control character is not.
     */
    @Test
    void whatEachClassCountsIsWhatTheRunTimeCountsAsNotWhitespace() {
        String ideographicSpace = "　";
        String noBreakSpace = " ";
        String bell = "\u0007";
        Object[][] expected = {
            // text, not whitespace, not whitespace and not a comma
            {"", 0, 0},
            {"   ", 0, 0},
            {",", 1, 0},
            {" , ", 1, 0},
            {ideographicSpace + "," + ideographicSpace, 1, 0},
            {noBreakSpace, 0, 0},
            {"  abc  ", 3, 3},
            {"a,b", 3, 2},
            {"Bug, bug , UI", 10, 8},
            {",,,", 3, 0},
            {bell, 1, 1},
            {"😀", 1, 1},
            {"😀,😀", 3, 2},
        };
        for (Object[] row : expected) {
            String text = (String) row[0];
            assertEquals(Count.of((int) row[1]), read(NOT_WHITESPACE, text),
                    "not whitespace, of " + show(text));
            assertEquals(Count.of((int) row[2]), read(NOT_WHITESPACE_NOR_COMMA, text),
                    "not whitespace nor a comma, of " + show(text));
        }
    }

    /** Only a string is read, and anything else holds no number of this kind. */
    @Test
    void whatIsNotAStringHoldsNoCount() {
        assertInstanceOf(NumericTerm.Reading.NotNumber.class,
                ordersOf(NOT_WHITESPACE).read(new ObservedValue.Integer(3)));
    }

    /**
     * What is built for a count reads back as that count, in either class, and a string of none
     * is written the ways a reader would try: with nothing, with whitespace, and with the
     * separator alone.
     */
    @Test
    void everyStringBuiltForACountReadsBackAsIt() {
        int checked = 0;
        for (CodePointClass counted : List.of(NOT_WHITESPACE, NOT_WHITESPACE_NOR_COMMA)) {
            TermOrders orders = ordersOf(counted);
            for (long each : new long[] {0, 1, 2, 3, 7}) {
                TermRealizations.Realization made = TermRealizations.at(Type.STRING, orders,
                        Count.of(each), NothingTheRulesSay.REGION, READING);
                TermRealizations.Realization.Built built = assertInstanceOf(
                        TermRealizations.Realization.Built.class, made,
                        counted + " holds " + each + " of its code points in some string");
                for (FixtureTemplate value : built.values()) {
                    assertEquals(new NumericTerm.Reading.Number(Count.of(each)),
                            orders.read(observed(value)),
                            "built " + value.text() + " for " + each + " of " + counted);
                    checked++;
                }
            }
        }
        assertTrue(checked > 0, "nothing was built, so nothing was read back");
    }

    /** None of them, written both ways a string of whitespace and separators is. */
    @Test
    void aStringOfNoneIsOfferedAsWhitespaceAndAsTheSeparatorToo() {
        List<String> offered = new ArrayList<>();
        TermRealizations.Realization.Built built = assertInstanceOf(
                TermRealizations.Realization.Built.class,
                TermRealizations.at(Type.STRING, ordersOf(NOT_WHITESPACE_NOR_COMMA), Count.of(0),
                        NothingTheRulesSay.REGION, READING));
        built.values().forEach(each -> offered.add(
                ((Hir.StringLit) each.value()).value()));
        assertTrue(offered.contains(""), offered.toString());
        assertTrue(offered.stream().anyMatch(text -> text.contains(",")), offered.toString());
        assertTrue(offered.stream().anyMatch(text -> text.contains(" ")), offered.toString());
    }

    private static Place read(CodePointClass counted, String text) {
        return assertInstanceOf(NumericTerm.Reading.Number.class,
                ordersOf(counted).read(new ObservedValue.Text(text))).value();
    }

    private static ObservedValue observed(FixtureTemplate value) {
        return new ObservedValue.Text(assertInstanceOf(Hir.StringLit.class, value.value())
                .value());
    }

    private static String show(String text) {
        StringBuilder out = new StringBuilder("\"");
        text.codePoints().forEach(cp -> out.append(cp > 32 && cp < 127
                ? String.valueOf((char) cp) : "U+%X".formatted(cp)));
        return out.append('"').toString();
    }
}
