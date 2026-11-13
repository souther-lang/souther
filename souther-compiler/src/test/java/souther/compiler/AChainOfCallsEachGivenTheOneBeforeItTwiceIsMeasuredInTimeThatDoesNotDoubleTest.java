package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.time.Duration;
import java.util.function.IntFunction;
import java.util.function.IntUnaryOperator;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An equality over the answer of the last of a chain of calls, each handed the one before it
 * twice, is measured in what grows with the calls and not with the paths through them.
 */
class AChainOfCallsEachGivenTheOneBeforeItTwiceIsMeasuredInTimeThatDoesNotDoubleTest {

    private static String reportOfChain(int depth, String comparison) {
        return reportOfChainEndingIn(depth, "LAST " + comparison + " j");
    }

    private static String reportOfChainEndingIn(int depth, String ending) {
        StringBuilder body = new StringBuilder("{\n    let a0 = x\n");
        for (int i = 1; i <= depth; i++) {
            body.append("    let a%d = Int.floorMod(a%d, a%d)\n".formatted(i, i - 1, i - 1));
        }
        body.append("    " + ending.replace("LAST", "a" + depth) + "\n}");
        Compilation compilation = Compilation.ofSource("""
                module m

                behavior f : (x: Int, j: Int) -> Bool
                let f (x, j) = %s
                """.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.ALL));
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String reportOfNamesThatReachEachOther(int depth) {
        StringBuilder body = new StringBuilder("{\n    let a0 = x\n    let b0 = j\n");
        for (int i = 1; i <= depth; i++) {
            body.append("    let a%d = Int.floorMod(a%d, b%d)\n".formatted(i, i - 1, i - 1));
            body.append("    let b%d = Int.floorMod(b%d, a%d)\n".formatted(i, i - 1, i - 1));
        }
        body.append("    a%d == b%d\n}".formatted(depth, depth));
        Compilation compilation = Compilation.ofSource("""
                module m

                behavior f : (x: Int, j: Int) -> Bool
                let f (x, j) = %s
                """.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.ALL));
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String reportOfTruthsEachMadeOfTheOneBefore(int depth, String step) {
        StringBuilder body = new StringBuilder("{\n    let a0 = x >= 0\n");
        for (int i = 1; i <= depth; i++) {
            body.append("    let a%d = %s\n".formatted(i, step.replace("PREV", "a" + (i - 1))));
        }
        body.append("    a%d\n}".formatted(depth));
        Compilation compilation = Compilation.ofSource("""
                module m

                behavior f : (x: Int, j: Int) -> Bool
                let f (x, j) = %s
                """.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.ALL));
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String reportOfNamesEachMadeOfTheOneBefore(int depth, String seed, String step,
                                                              String ending) {
        StringBuilder body = new StringBuilder("{\n    let a0 = " + seed + "\n");
        for (int i = 1; i <= depth; i++) {
            body.append("    let a%d = %s\n".formatted(i, step.replace("PREV", "a" + (i - 1))));
        }
        body.append("    " + ending.replace("LAST", "a" + depth) + "\n}");
        Compilation compilation = Compilation.ofSource("""
                module m

                behavior f : (x: Int, j: Int) -> Bool
                let f (x, j) = %s
                """.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.ALL));
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void aProductOfANameWithItselfSaysAtAnyDepthWhatItSaysAtAShallowOne() {
        assertSaysAtAnyDepthWhatItSaysAtAShallowOne(
                depth -> reportOfNamesEachMadeOfTheOneBefore(depth, "x", "PREV * PREV",
                        "LAST >= j"),
                AChainOfCallsEachGivenTheOneBeforeItTwiceIsMeasuredInTimeThatDoesNotDoubleTest
                        ::afterOneLetEachCall, 3, 50);
    }

    /** What a remainder of a sum of a name with itself says depends on the depth, as the numbers it
     *  is of do; what is asked here is that it is worked out in time that does not double. */
    @Test
    void aRemainderOfASumOfANameWithItselfIsReadInTimeThatDoesNotDoubleWithTheDepth() {
        String report = assertTimeoutPreemptively(Duration.ofSeconds(60),
                () -> reportOfNamesEachMadeOfTheOneBefore(50, "x",
                        "Int.floorMod(PREV + PREV, 7)", "LAST >= j"));
        assertTrue(!report.isEmpty(), "a report is made");
    }

    @Test
    void aTruthMadeOfANameOnBothSidesOfADisjunctionIsReadInTimeThatDoesNotDoubleWithTheDepth() {
        String report = assertTimeoutPreemptively(Duration.ofSeconds(60),
                () -> reportOfNamesEachMadeOfTheOneBefore(22, "x >= 0",
                        "PREV && (j > 3 || PREV)", "LAST"));
        assertTrue(!report.isEmpty(), "a report is made");
    }

    /** What is said of a truth does not depend on how many names it is made through. */
    @Test
    void aTruthMadeOfTheOneBeforeItTwiceIsReadOnceForEachNameAndSaysWhatItSaysAtAnyDepth() {
        for (String step : new String[] {"PREV && PREV", "PREV || PREV",
                "if PREV then PREV else PREV"}) {
            String shallow = reportOfTruthsEachMadeOfTheOneBefore(2, step);
            String deep = assertTimeoutPreemptively(Duration.ofSeconds(60),
                    () -> reportOfTruthsEachMadeOfTheOneBefore(100, step));
            assertEquals(shallow, deep, step);
        }
    }

    /** A place in the report, as {@code line:column} or with the file before: {@code 9:8},
     *  {@code 0:9:8}. */
    private static final Pattern PLACE = Pattern.compile("(?<![\\d:])(?:\\d+:)?(\\d+):(\\d+)(?!\\d)");

    /**
     * The report with the places on the line the comparison is written on taken out: that line is
     * further down in a deeper chain, and is all that differs between two depths. Every other place
     * in the report is compared as it stands, and there must be one on that line to take out.
     */
    private static String withTheComparisonsPlaceTakenOut(String report, int line) {
        Matcher places = PLACE.matcher(report);
        boolean found = false;
        while (places.find()) {
            found |= Integer.parseInt(places.group(1)) == line;
        }
        assertTrue(found, "the report says where the comparison is, on line " + line);
        return PLACE.matcher(report).replaceAll(each ->
                Integer.parseInt(each.group(1)) == line ? "L:C" : Matcher.quoteReplacement(
                        each.group()));
    }

    private static void assertSaysAtAnyDepthWhatItSaysAtAShallowOne(
            IntFunction<String> reportAt, IntUnaryOperator lineOfTheComparison, int shallow,
            int... deep) {
        String expected = withTheComparisonsPlaceTakenOut(reportAt.apply(shallow),
                lineOfTheComparison.applyAsInt(shallow));
        for (int depth : deep) {
            String report = assertTimeoutPreemptively(Duration.ofSeconds(60),
                    () -> reportAt.apply(depth));
            assertEquals(expected, withTheComparisonsPlaceTakenOut(report,
                    lineOfTheComparison.applyAsInt(depth)), "depth " + depth);
        }
    }

    /** The source puts the module, the behavior and the first name on five lines, then a line for
     *  each call, and the comparison on the next. */
    private static int afterOneLetEachCall(int depth) {
        return depth + 6;
    }

    /** The same, with two names to begin with and two lines for each call. */
    private static int afterTwoLetsEachCall(int depth) {
        return 2 * depth + 7;
    }

    @Test
    void aChainNamedInTheConditionOfAnIfAndInItsArmsSaysAtAnyDepthWhatItSaysAtAShallowOne() {
        assertSaysAtAnyDepthWhatItSaysAtAShallowOne(
                depth -> reportOfChainEndingIn(depth,
                        "if LAST == j then LAST > 1 else LAST < j"),
                AChainOfCallsEachGivenTheOneBeforeItTwiceIsMeasuredInTimeThatDoesNotDoubleTest
                        ::afterOneLetEachCall, 3, 24, 60);
    }

    @Test
    void namesThatReachEachOtherSayAtAnyDepthWhatTheySayAtAShallowOne() {
        assertSaysAtAnyDepthWhatItSaysAtAShallowOne(
                depth -> reportOfNamesThatReachEachOther(depth),
                AChainOfCallsEachGivenTheOneBeforeItTwiceIsMeasuredInTimeThatDoesNotDoubleTest
                        ::afterTwoLetsEachCall, 3, 40);
    }

    @Test
    void anEqualityOverAChainSaysAtAnyDepthWhatItSaysAtAShallowOne() {
        assertSaysAtAnyDepthWhatItSaysAtAShallowOne(
                depth -> reportOfChain(depth, "=="),
                AChainOfCallsEachGivenTheOneBeforeItTwiceIsMeasuredInTimeThatDoesNotDoubleTest
                        ::afterOneLetEachCall, 3, 24, 40, 100);
    }

    @Test
    void anOrderOverAChainSaysAtAnyDepthWhatItSaysAtAShallowOne() {
        assertSaysAtAnyDepthWhatItSaysAtAShallowOne(
                depth -> reportOfChain(depth, ">="),
                AChainOfCallsEachGivenTheOneBeforeItTwiceIsMeasuredInTimeThatDoesNotDoubleTest
                        ::afterOneLetEachCall, 3, 24, 100);
    }
}
