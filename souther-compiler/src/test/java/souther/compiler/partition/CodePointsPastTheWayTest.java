package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.regex.Language;
import souther.compiler.regex.PatternPlan;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.types.Type;
import souther.compiler.values.ValueSet;

import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.Meter;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The strings that hold a number of the code points of a class are those the count says, and the
 * strings outside are every other: for each class and each pair of ends, over every string of a
 * few code points that are in the class, out of it, and outside the basic plane.
 */
class CodePointsPastTheWayTest {

    private static final List<String> LETTERS = List.of("a", " ", "b", "\t", "é", "😀");

    private static final CodePointClass NOT_WHITESPACE = new CodePointClass.NotWhitespace();

    private static final CodePointClass AS = new CodePointClass.OneOf(CodePoints.of('a'));

    private static final CodePointClass NOT_WHITESPACE_NOR_A =
            new CodePointClass.NotWhitespaceNorEqualTo('a');

    /** Every string of up to {@code longest} of the letters. */
    private static List<String> strings(int longest) {
        List<String> out = new ArrayList<>();
        out.add("");
        List<String> layer = List.of("");
        for (int length = 1; length <= longest; length++) {
            List<String> next = new ArrayList<>();
            for (String each : layer) {
                for (String letter : LETTERS) {
                    next.add(each + letter);
                }
            }
            out.addAll(next);
            layer = next;
        }
        return out;
    }

    private static long held(CodePointClass counted, String string) {
        return string.codePoints().filter(counted::contains).count();
    }

    private static Language compiled(PatternPlan plan) {
        Language language = plan.compile(PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter());
        assertNotNull(language);
        return language;
    }

    private static CodePointsPastTheWay counted(CodePointClass counted, Integer least,
                                                Integer most) {
        return new CodePointsPastTheWay(counted, new LengthsPastTheWay.Lengths(
                least == null ? null : BigInteger.valueOf(least),
                most == null ? null : BigInteger.valueOf(most)));
    }

    /** A string is among these exactly when it holds that many of the class, and among the rest
     *  exactly when it does not. */
    @Test
    void aStringIsOfTheCountsExactlyWhenItHoldsThatManyOfTheClass() {
        List<String> corpus = strings(4);
        for (CodePointClass counted : List.of(NOT_WHITESPACE, AS, NOT_WHITESPACE_NOR_A)) {
            for (int[] ends : new int[][] {{1, -1}, {0, 0}, {2, 5}, {3, 3}, {0, 2}, {1, 1}, {4, -1}}) {
                CodePointsPastTheWay counts = counted(counted, ends[0], ends[1] < 0 ? null : ends[1]);
                Language within = compiled(counts.strings());
                PatternPlan outsidePlan = counts.stringsOutside();
                assertNotNull(outsidePlan, () -> counted + " " + List.of(ends[0], ends[1]));
                Language outside = compiled(outsidePlan);
                for (String string : corpus) {
                    boolean holds = held(counted, string) >= ends[0]
                            && (ends[1] < 0 || held(counted, string) <= ends[1]);
                    String said = counted + " " + ends[0] + ".." + ends[1] + " " + string.length();
                    assertEquals(holds, within.has(string), () -> said + " within");
                    assertEquals(!holds, outside.has(string), () -> said + " outside");
                }
            }
        }
    }

    /** The strings short of the least and those past the most are told apart, each with the
     *  bound it is open for, so that a reader is told which. */
    @Test
    void theStringsOutsideAreToldApartByWhichEndTheyAreShortOf() {
        List<CodePointsPastTheWay.Open> open = counted(NOT_WHITESPACE, 2, 5).outside();
        assertEquals(2, open.size());
        assertEquals(2L, open.get(0).why().fewerThan());
        assertNull(open.get(0).why().moreThan());
        assertEquals(5L, open.get(1).why().moreThan());
        assertNull(open.get(1).why().fewerThan());
        Language fewer = compiled(open.get(0).strings());
        Language more = compiled(open.get(1).strings());
        for (String string : strings(4)) {
            long many = held(NOT_WHITESPACE, string);
            assertEquals(many < 2, fewer.has(string), string);
            assertEquals(many > 5, more.has(string), string);
        }
    }

    /** Nothing is open where every count is allowed, and no end is said that no string reaches. */
    @Test
    void nothingIsOutsideWhereEveryCountIsAllowed() {
        CodePointsPastTheWay all = counted(NOT_WHITESPACE, null, null);
        assertTrue(all.outside().isEmpty());
        assertNull(all.stringsOutside());
        assertTrue(compiled(all.strings()).has("  a "));
        assertTrue(compiled(all.strings()).has(""));
    }

    /** No string is of counts that leave none, and every string is outside them. */
    @Test
    void noStringHasACountThatLeavesNone() {
        CodePointsPastTheWay none = counted(NOT_WHITESPACE, 3, 1);
        assertTrue(none.isEmpty());
        assertNull(none.strings());
    }

    private static NumericTerm.FromOnePosition countAt(String place) {
        Symbols symbols = Symbols.none(DefaultStdlib.get());
        return NumericTerm.CodePointClassCount.of(TermPath.of(place), NOT_WHITESPACE,
                CaseMapping.NONE, Type.STRING, ScopedDeclarations.wrapsOf(symbols));
    }

    private static TakenConstraint statement(long constant, Rel rel,
                                             Map<NumericTerm, Long> weights) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        weights.forEach((term, weight) -> coefs.put(term, ExactRatio.of(weight)));
        return new TakenConstraint.Affine(new LinearForm<>(ExactRatio.of(constant), coefs), rel);
    }

    /** The count of a class is eliminated against the numbers beside it as a length is: with
     *  {@code n} between nought and one, three code points of the class less {@code n} are two
     *  at least, and the strings of those counts are the ones holding two. */
    @Test
    void aNumberBesideTheCountOfAClassIsTakenOutAsOneBesideALengthIs() {
        NumericTerm count = countAt("s");
        NumericTerm n = new NumericTerm.ValueOf(TermPath.of("n"));
        LengthsPastTheWay.Lengths counts = LengthsPastTheWay.of(count, List.of(
                statement(-3, Rel.GE, Map.of(count, 1L, n, 1L))),
                _ -> new LengthsPastTheWay.Ends(BigInteger.ZERO, BigInteger.ONE));

        assertNotNull(counts);
        assertEquals(BigInteger.TWO, counts.least());
        Language within = compiled(new CodePointsPastTheWay(NOT_WHITESPACE, counts).strings());
        for (String string : strings(4)) {
            assertEquals(held(NOT_WHITESPACE, string) >= 2, within.has(string), string);
        }
    }

    /** What the counts allow and which strings exist are two questions: the strings a place
     *  holds are met with the counts, and a string of it that holds too few is not among them. */
    @Test
    void theStringsAPlaceHoldsAreMetWithTheCountsAndNotTakenFromThem() {
        Meter meter = PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter();
        Language place = Language.ofWords(List.of(" ", "a ", "ab", ""), meter);
        Language reaching = Partitions.ofTheLengths(place,
                counted(NOT_WHITESPACE, 1, null), meter);
        assertNotNull(reaching);
        assertTrue(reaching.has("a "));
        assertTrue(reaching.has("ab"));
        assertFalse(reaching.has(" "));
        assertFalse(reaching.has(""));
    }

    /** A class that counts no code point allows counts that no string holds: the counts are not
     *  empty, and the strings of them are. */
    @Test
    void aClassOfNoCodePointAllowsCountsNoStringHolds() {
        CodePointClass none = new CodePointClass.OneOf(CodePoints.NONE);
        CodePointsPastTheWay atLeastOne = counted(none, 1, null);
        assertFalse(atLeastOne.isEmpty());
        assertTrue(compiled(atLeastOne.strings()).isEmpty());
        CodePointsPastTheWay any = counted(none, 0, null);
        assertTrue(compiled(any.strings()).has("abc"));
    }

    /** What is shown of a partner is changed without losing the reach it was given: a value built
     *  again from the strings alone is shown at every length. */
    @Test
    void showingOtherStringsKeepsTheReachAndTheOpenOperations() {
        CodePointsPastTheWay reached = counted(NOT_WHITESPACE, 1, null);
        CodePointsPastTheWay held = counted(NOT_WHITESPACE, 2, null);
        UndividedByARelation.StringsAPartnerCanHold shown =
                new UndividedByARelation.StringsAPartnerCanHold(ValueSet.ANY, ValueSet.ANY, null,
                        reached, held, "b", List.of("String.uppercase"));

        UndividedByARelation.StringsAPartnerCanHold other =
                shown.showing(ValueSet.NONE, ValueSet.ANY, 3L);

        assertEquals(ValueSet.NONE, other.canBe());
        assertEquals(3L, other.upTo());
        assertEquals(reached, other.reached());
        assertEquals(held, other.partnerHeldTo());
        assertEquals("b", other.partner());
        assertEquals(List.of("String.uppercase"), other.imagesNotShown());
    }

    /** A count the allowance does not pay to build is not built, and no string is called of it
     *  or outside it on a language that was not made. */
    @Test
    void aCountTheAllowanceWillNotPayForIsNotBuilt() {
        CodePointsPastTheWay huge = counted(NOT_WHITESPACE, 100_000_000, null);
        assertNull(huge.strings().compile(PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter()));
        assertNull(huge.stringsOutside()
                .compile(PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter()));
    }
}
