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
import static org.junit.jupiter.api.Assertions.assertFalse;
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
                        ::afterOneLetEachCall, 3, 30);
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

    private static String reportOfSizesAddedToThemselves(int depth, String ending) {
        StringBuilder body = new StringBuilder("{\n    let a0 = String.length(s)\n");
        for (int i = 1; i <= depth; i++) {
            body.append("    let a%d = a%d + a%d\n".formatted(i, i - 1, i - 1));
        }
        body.append("    " + ending.replace("LAST", "a" + depth) + "\n}");
        Compilation compilation = Compilation.ofSource("""
                module m

                behavior f : (s: String, j: Int) -> Bool
                let f (s, j) = %s
                """.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.ALL));
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /**
     * Held against a number that parts nought from the rest, a size added to itself is the check
     * of one container however many names it is added through.
     */
    @Test
    void aSizeAddedToItselfThroughAChainOfNamesSaysAtAnyDepthWhatItSaysAtAShallowOne() {
        for (String ending : new String[] {"LAST == 0", "LAST > 0", "LAST /= 0"}) {
            assertSaysAtAnyDepthWhatItSaysAtAShallowOne(
                    depth -> reportOfSizesAddedToThemselves(depth, ending),
                    AChainOfCallsEachGivenTheOneBeforeItTwiceIsMeasuredInTimeThatDoesNotDoubleTest
                            ::afterOneLetEachCall, 3, 24);
        }
    }

    /**
     * A hundred additions overflow an Int, and the run that would add them stops there: the
     * sum is nought exactly where every size is, but the arithmetic the program writes is read
     * from what is written and not from the sizes it comes to, so the stop is still said.
     */
    @Test
    void aSizeAddedToItselfAHundredTimesIsStillSaidToStopAtTheOverflow() {
        String report = assertTimeoutPreemptively(Duration.ofSeconds(60),
                () -> reportOfSizesAddedToThemselves(100, "LAST == j"));
        Pattern overflow = Pattern.compile("\\? nothing could show .*Int overflow: (\\d+) \\+ \\1\\)");
        assertTrue(overflow.matcher(report).find(), report);
        assertTrue(report.contains("adequacy: undetermined"), report);
    }

    /** And where the sum is held against nought the stop is the same, whatever the sum is read as. */
    @Test
    void aSizeAddedToItselfAHundredTimesHeldAtNoughtStopsAtTheOverflowToo() {
        String report = assertTimeoutPreemptively(Duration.ofSeconds(60),
                () -> reportOfSizesAddedToThemselves(100, "LAST == 0"));
        assertTrue(Pattern.compile("Int overflow: (\\d+) \\+ \\1").matcher(report).find(), report);
    }

    /** A depth below the end of Int has no stop to say. */
    @Test
    void aSizeAddedToItselfTwentyFourTimesSaysNoStop() {
        String report = reportOfSizesAddedToThemselves(24, "LAST == j");
        assertFalse(report.contains("Int overflow"), report);
    }
}
