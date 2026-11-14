package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.Compiler;
import souther.compiler.query.Adequacy;
import souther.test.Growth;

import java.util.LinkedHashMap;
import java.util.SequencedMap;
import java.util.function.Consumer;
import java.util.function.IntFunction;
import java.util.function.UnaryOperator;

/**
 * A body may be as deep as a definition holds ({@code source-structural-complexity-is-bounded}), so
 * a chain of {@code let}s that each use the one before it, once or twice, is a source the language
 * accepts. What it asks of the compiler is work that grows with the length of the chain, not with
 * the ways down it (which double with each link) and not with their square or cube.
 *
 * <p>Held as the work the reading counts and not as how long it takes: the names read afresh, the
 * walks a reading starts, and the nodes those walks name. Each step from a chain to a longer one
 * must leave the work at most three times where the chain is twice as long: a linear
 * reading doubles, the square is four times, and a reading made once per way is far more.
 */
class AChainOfLetsIsReadInWorkThatGrowsWithItsLengthTest {

    private static final int[] LINKS = {2, 4, 8, 16};

    private static String chain(int links, String seed, String step, String ending,
                                String parameters) {
        StringBuilder body = new StringBuilder("{\n    let a0 = " + seed + "\n");
        for (int i = 1; i <= links; i++) {
            body.append("    let a%d = %s\n".formatted(i, step.replace("PREV", "a" + (i - 1))));
        }
        body.append("    " + ending.replace("LAST", "a" + links) + "\n}");
        return "module m\n\nbehavior f : (%s) -> Bool\nlet f (%s) = %s\n".formatted(parameters,
                parameters.replaceAll(": \\w+", ""), body);
    }

    private static String ofInts(int links, String step, String ending) {
        return chain(links, "x", step, ending, "x: Int, j: Int");
    }

    /** What {@code reading} the source came to: names read afresh, walks started and nodes named. */
    private static long workOver(String source, Consumer<String> reading) {
        long[] names = {0};
        long[] walks = {0};
        long[] named = {0};
        AffineForms.NAMES_READ = names;
        Terms.COUNTING_WALKS = walks;
        Terms.COUNTING_NAMED = named;
        try {
            reading.accept(source);
        } finally {
            AffineForms.NAMES_READ = null;
            Terms.COUNTING_WALKS = null;
            Terms.COUNTING_NAMED = null;
        }
        return names[0] + walks[0] + named[0];
    }

    private static void assertGrowsWithTheLength(IntFunction<String> chainOf) {
        assertGrowsWithTheLength(chainOf, source -> ACompiledModel.measured(source,
                Adequacy.Asked.reportOnly(Adequacy.Level.ALL)));
    }

    private static void assertGrowsWithTheLength(IntFunction<String> chainOf,
                                                 Consumer<String> reading) {
        SequencedMap<Integer, Long> work = new LinkedHashMap<>();
        for (int links : LINKS) {
            work.put(links, workOver(chainOf.apply(links), reading));
            // Asked as each is counted, so a reading that doubles with every link is refused at the
            // shortest chains and does not go on to count the longest.
            Growth.eachAtMost(work, 3, 1);
        }
    }

    @Test
    void aChainOfCallsEachGivenTheOneBeforeItTwice() {
        assertGrowsWithTheLength(links -> ofInts(links, "Int.floorMod(PREV, PREV)", "LAST == j"));
        assertGrowsWithTheLength(links -> ofInts(links, "Int.floorMod(PREV, PREV)", "LAST >= j"));
    }

    @Test
    void aChainOfRemaindersEachOverTheOneBeforeAddedToItself() {
        assertGrowsWithTheLength(links -> ofInts(links, "Int.floorMod(PREV + PREV, 7)", "LAST == j"));
        assertGrowsWithTheLength(links -> ofInts(links, "Int.floorMod(PREV + PREV, 7)", "LAST >= j"));
    }

    @Test
    void aChainOfProducts() {
        assertGrowsWithTheLength(links -> ofInts(links, "PREV * PREV", "LAST >= j"));
    }

    @Test
    void aChainNamedInTheConditionOfAnIfAndInItsArms() {
        assertGrowsWithTheLength(links -> ofInts(links, "Int.floorMod(PREV, PREV)",
                "if LAST == j then LAST > 1 else LAST < j"));
    }

    @Test
    void aChainOfTruthsEachMadeOfTheOneBefore() {
        for (String step : new String[] {"PREV && PREV", "PREV || PREV",
                "if PREV then PREV else PREV", "PREV && (j > 3 || PREV)"}) {
            assertGrowsWithTheLength(links -> chain(links, "x >= 0", step, "LAST", "x: Int, j: Int"));
        }
    }

    @Test
    void aChainOfSizesAddedToThemselves() {
        assertGrowsWithTheLength(links ->
                chain(links, "String.length(s)", "PREV + PREV", "LAST == j", "s: String, j: Int"));
    }

    @Test
    void twoChainsThatReachEachOther() {
        assertGrowsWithTheLength(links -> {
            StringBuilder body = new StringBuilder("{\n    let a0 = x\n    let b0 = j\n");
            for (int i = 1; i <= links; i++) {
                body.append("    let a%d = Int.floorMod(a%d, b%d)\n".formatted(i, i - 1, i - 1));
                body.append("    let b%d = Int.floorMod(b%d, a%d)\n".formatted(i, i - 1, i - 1));
            }
            body.append("    a%d == b%d\n}".formatted(links, links));
            return "module m\n\nbehavior f : (x: Int, j: Int) -> Bool\nlet f (x, j) = " + body + "\n";
        });
    }

    @Test
    void aChainOfCaseConversionsRunInOneDirectionOrBetweenTwo() {
        for (boolean alternating : new boolean[] {false, true}) {
            assertGrowsWithTheLength(links -> {
                StringBuilder body = new StringBuilder("{\n");
                for (int i = 1; i <= links; i++) {
                    body.append("  let a%d = String.%s(%s)\n".formatted(i,
                            alternating && i % 2 == 0 ? "uppercase" : "lowercase",
                            i == 1 ? "i" : "a" + (i - 1)));
                }
                body.append("  a%d == j\n}".formatted(links));
                return "module chain\n\nbehavior f : (i: String, j: String) -> Bool\n\n"
                        + "let f (i, j) = " + body + "\n";
            });
        }
    }

    /** {@code links} values of the module, each {@code link} of the one before it, and an
     *  invariant stating {@code rule} of the last. */
    private static String valuesOfTheModule(int links, String first, UnaryOperator<String> link,
                                             String rule, String type) {
        StringBuilder source = new StringBuilder("module m exposing ( D, f )\n\nlet c0 = " + first + "\n");
        for (int at = 1; at <= links; at++) {
            source.append("let c%d = %s\n".formatted(at, link.apply("c" + (at - 1))));
        }
        return source + """

                data D = %s
                    invariant %s

                behavior f : (d: D) -> Int
                let f (d) = 1
                """.formatted(type, rule.replace("LAST", "c" + links));
    }

    private static void assertCompiledInWorkThatGrowsWithTheLength(IntFunction<String> chainOf) {
        assertGrowsWithTheLength(chainOf, Compiler::compile);
    }

    /** Each value names the one before it twice, and an invariant names the last of them, whichever
     *  of the representations of the clause reads it: nothing copies a value for each name. */
    @Test
    void anInvariantNamingTheLastOfAChainOfValuesEachNamingTheOneBeforeItTwice() {
        UnaryOperator<String> twice = previous -> previous + " + " + previous;
        assertCompiledInWorkThatGrowsWithTheLength(links ->
                valuesOfTheModule(links, "2", twice, "value > LAST", "Int"));
        assertCompiledInWorkThatGrowsWithTheLength(links ->
                valuesOfTheModule(links, "2", twice, "Int.compare(value, LAST) <= 0", "Int"));
        assertCompiledInWorkThatGrowsWithTheLength(links ->
                valuesOfTheModule(links, "2", twice, "Int.compare(value, 5) + LAST <= LAST", "Int"));
        assertCompiledInWorkThatGrowsWithTheLength(links ->
                valuesOfTheModule(links, "true", previous -> previous + " && " + previous, "LAST",
                        "Int"));
        assertCompiledInWorkThatGrowsWithTheLength(links ->
                valuesOfTheModule(links, "0.1m", previous -> previous + " * " + previous,
                        "value > LAST", "Decimal"));
        assertCompiledInWorkThatGrowsWithTheLength(links ->
                valuesOfTheModule(links, "2", previous -> "Int.min(" + previous + ", " + previous + ")",
                        "value > LAST", "Int"));
    }

    @Test
    void aBodyOrAnEnsuresNamingTheLastOfAChainOfValuesEachNamingTheOneBeforeItTwice() {
        IntFunction<String> doubling = links -> {
            StringBuilder chain = new StringBuilder("module m exposing ( f )\n\nlet c0 = 2\n");
            for (int at = 1; at <= links; at++) {
                chain.append("let c%d = c%d + c%d\n".formatted(at, at - 1, at - 1));
            }
            return chain.toString();
        };
        assertCompiledInWorkThatGrowsWithTheLength(links -> doubling.apply(links)
                + "\nbehavior f : (n: Int) -> Int\nlet f (n) = n + c" + links + "\n");
        assertCompiledInWorkThatGrowsWithTheLength(links -> doubling.apply(links)
                + "\nlet h (n: Int) = n + c" + links
                + "\nbehavior f : (n: Int) -> Int\nlet f (n) = h(n)\n");
        assertCompiledInWorkThatGrowsWithTheLength(links -> doubling.apply(links)
                + "\nlet h (x) = x + c" + links
                + "\nbehavior f : (n: Int) -> Int\nlet f (n) = h(n)\n");
        assertCompiledInWorkThatGrowsWithTheLength(links -> doubling.apply(links)
                + "\nbehavior f : (n: Int) -> Int\n    ensures value > n + c" + links
                + "\nlet f (n) = n + c" + links + " + 1\n");
    }

    /** A body that binds {@code before}, then compares two places no stop in it reads. */
    private static String withAStopIn(String before) {
        return """
                module probe.arm

                data Row = { x: Int, k: Int, m: Int, j: Int }

                behavior m : (p: Row) -> Bool
                let m (p) = {
                    %s
                    let c = p.m + 1 >= p.j
                    c
                }
                """.formatted(before);
    }

    @Test
    void aChainOfNamesEachReadingAQuotientOfTheOneBeforeTwice() {
        assertGrowsWithTheLength(links -> {
            StringBuilder before = new StringBuilder("let a0 = 1 / p.x");
            for (int i = 1; i <= links; i++) {
                before.append("\n    let a%d = a%d * a%d".formatted(i, i - 1, i - 1));
            }
            return withAStopIn(before + "\n    let y = Rational.toInt(DOWN, a" + links + ")");
        });
    }

    @Test
    void aChainOfNamesEachHoldingARemainderOfTheOneBeforeAndThatOneBeside() {
        assertGrowsWithTheLength(links -> {
            StringBuilder before = new StringBuilder("let a0 = p.x");
            for (int i = 1; i <= links; i++) {
                before.append("\n    let a%d = Int.floorMod(a%d, 7) + a%d".formatted(i, i - 1, i - 1));
            }
            return withAStopIn(before + "\n    let y = Int.floorMod(7, a" + links + ")");
        });
    }
}
