package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.regex.Language;
import souther.compiler.regex.PatternPlan;
import souther.compiler.semantics.CodePointClass;

import net.unit8.notation199x.pattern.CodePoints;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
