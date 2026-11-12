package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.BiPredicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison read past an operation that stops a run is read over the inputs that get past it,
 * held against the runs themselves.
 *
 * <p>Each model works out something that may stop a run, and compares. Two different things are
 * asked of the runs, and they are not the same set of rows. A row <em>gets to</em> the comparison
 * where what is worked out before it completes, which is the behavior cut off there and run; and a
 * row <em>completes</em> it where the whole behavior does, which also holds what the comparison
 * itself works out. The analysis is held to the first for what it says reaches the comparison, and
 * to the second for what it says may stop a run in it.
 *
 * <p>And what the comparison states is held to be what it states without the operation before
 * it: the lines it draws are those of the same comparison written alone, and every row it is owed
 * is a row that gets to it.
 */
class AComparisonReadPastAStoppingOperationIsReadOverTheInputsThatGetPastItTest {

    private static final String MODULE = "probe.stop";

    private static final String DECLARED = """
            module probe.stop

            data Ok
            data No
            data Skipped

            data Pair = { x: Int, k: Int }
            """;

    private static final long GREATEST = Long.MAX_VALUE;

    /** The values each field of a row of the grid takes, beside the greatest {@code Int}, which a
     *  sum past it stops at. */
    private static final long[] VALUES = {-3, -2, -1, 0, 1, 2, 3, GREATEST};

    /** The values of {@link #VALUES} with others of it below and above. */
    private static final long[] INSIDE = {-2, -1, 0, 1, 2};

    /**
     * One model.
     *
     * @param before       what is worked out before the comparison
     * @param comparison   the comparison
     * @param after        what is worked out after it, whose stops the comparison does not turn on
     * @param gets         where a row gets to the comparison, which is where {@code before}
     *                     completes
     * @param completes    where the whole behavior completes
     * @param unread       whether what the operation says of where it answers is no more than the
     *                     reading can use, so that the comparison is not read
     * @param asItsOwn     whether the comparison draws the lines it draws alone
     */
    private record Case(String name, String before, String comparison, String after,
                        BiPredicate<Long, Long> gets, BiPredicate<Long, Long> completes,
                        boolean unread, boolean asItsOwn) {}

    private static final String QUOTIENT = "let y = Rational.toInt(DOWN, 1 / %s)";

    /** Whether {@code x + 1} is past the greatest {@code Int}, which stops a run. */
    private static boolean overflows(long x) {
        return x == GREATEST;
    }

    /** Whether a run works out {@code x + k} and gets past it: the sum is an {@code Int}. */
    private static boolean sumAnswers(long x, long k) {
        try {
            Math.addExact(x, k);
            return true;
        } catch (ArithmeticException past) {
            return false;
        }
    }

    private static final List<Case> CASES = List.of(
            new Case("a quotient by x, then x and k related",
                    QUOTIENT.formatted("p.x"), "p.x + 1 >= p.k", "",
                    (x, k) -> x != 0, (x, k) -> x != 0 && !overflows(x), false, true),
            new Case("a quotient by x, then k alone",
                    QUOTIENT.formatted("p.x"), "p.k >= 5", "",
                    (x, k) -> x != 0, (x, k) -> x != 0, false, true),
            new Case("a quotient by x, then x alone",
                    QUOTIENT.formatted("p.x"), "p.x + 1 >= 5", "",
                    (x, k) -> x != 0, (x, k) -> x != 0 && !overflows(x), false, true),
            new Case("a quotient by k, then x alone",
                    QUOTIENT.formatted("p.k"), "p.x + 1 >= 5", "",
                    (x, k) -> k != 0, (x, k) -> k != 0 && !overflows(x), false, true),
            new Case("a quotient by nought, then x and k related",
                    QUOTIENT.formatted("0"), "p.x + 1 >= p.k", "",
                    (x, k) -> false, (x, k) -> false, false, false),
            new Case("a quotient by what is no form, then x and k related",
                    QUOTIENT.formatted("(if p.x > 0 then p.x else 0)"), "p.x + 1 >= p.k", "",
                    (x, k) -> x > 0, (x, k) -> x > 0 && !overflows(x), true, false),
            new Case("a quotient by a sum of x and k, then x and k related",
                    QUOTIENT.formatted("(p.x + p.k)"), "p.x + 1 >= p.k", "",
                    (x, k) -> sumAnswers(x, k) && x + k != 0,
                    (x, k) -> sumAnswers(x, k) && x + k != 0 && !overflows(x), true, false),
            // What a run works out after the comparison stops no run that gets to it.
            new Case("a quotient by x after the comparison",
                    "", "p.x + 1 >= p.k", QUOTIENT.formatted("p.x"),
                    (x, k) -> true, (x, k) -> x != 0 && !overflows(x), false, true),
            // Where the quotient is worked out on some runs, it stops only those.
            new Case("a quotient by x worked out only where k is above nought",
                    "let y = if p.k > 0 then Rational.toInt(DOWN, 1 / p.x) else 0",
                    "p.x + 1 >= p.k", "",
                    (x, k) -> k <= 0 || x != 0,
                    (x, k) -> (k <= 0 || x != 0) && !overflows(x), true, false));

    /** {@code before}, the comparison and what follows, written as the body of {@code m}. */
    private static String body(String before, String comparison, String after) {
        return """
                {
                    %s
                    let c = %s
                    %s
                    c
                }""".formatted(before, comparison, after);
    }

    private static String source(Map<String, String> behaviors) {
        StringBuilder source = new StringBuilder(DECLARED);
        behaviors.forEach((name, body) -> source.append("""

                behavior %1$s : (p: Pair) -> Bool
                let %1$s (p) = %2$s
                """.formatted(name, body)));
        return source.toString();
    }

    private static Compilation measured(String source, Adequacy.Level level) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(level));
        compilation.answerEverything();
        return compilation;
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** Whether the report says some comparison has no row arrive at it. */
    private static boolean nothingArrives(String report) {
        return report.contains("no row that arrives at it");
    }

    private static boolean somethingIsNotRead(String report) {
        return report.contains("not read:");
    }

    /** Whether the report says a run that reaches some comparison may stop in what it works out. */
    private static boolean mayStop(String report) {
        return report.contains("may stop a run:");
    }

    /** The rows of the grid a run of {@code behavior} gets to the end of. */
    private static List<List<Long>> rowsThatFinish(BytesClassLoader loader, String behavior)
            throws Exception {
        Object built = Emitted.behavior(loader, MODULE, behavior).getConstructor().newInstance();
        List<List<Long>> past = new ArrayList<>();
        for (long x : VALUES) {
            for (long k : VALUES) {
                if (finishes(loader, built, x, k)) {
                    past.add(List.of(x, k));
                }
            }
        }
        return past;
    }

    private static boolean finishes(BytesClassLoader loader, Object behavior, long x, long k)
            throws Exception {
        Object row = Codecs.decoded(loader, MODULE + ".Pair", Map.of("x", x, "k", k));
        try {
            Codecs.apply(behavior, row);
            return true;
        } catch (RuntimeException stopped) {
            return false;
        }
    }

    private static List<List<Long>> rowsWhere(BiPredicate<Long, Long> holds) {
        List<List<Long>> rows = new ArrayList<>();
        for (long x : VALUES) {
            for (long k : VALUES) {
                if (holds.test(x, k)) {
                    rows.add(List.of(x, k));
                }
            }
        }
        return rows;
    }

    /** The lines the comparisons of {@code m} draw, each as the cut it is and the points it is
     *  owed, so that two readings are the one relation where these are the same. */
    private static List<String> linesOf(Compilation compilation) {
        List<BorderAssessment> lines = Adequacy.readingsOf(compilation.db(), MODULE).get("m");
        List<String> cuts = new ArrayList<>();
        if (lines != null) {
            for (BorderAssessment line : lines) {
                cuts.add(line.border().cut() + " " + new TreeSet<>(line.items().keySet().stream()
                        .map(String::valueOf).toList()));
            }
        }
        return cuts.stream().sorted().toList();
    }

    /**
     * What the language says stops a run is what runs stop at, so that the grid is an oracle of
     * which rows get to the comparison and which complete it; and the report is held to it, and
     * so are the lines it draws.
     */
    @Test
    void theReadingIsHeldToTheRowsThatGetToTheComparisonAndTheLinesItDrawsAlone()
            throws Exception {
        List<String> wrong = new ArrayList<>();
        for (Case each : CASES) {
            String whole = body(each.before(), each.comparison(), each.after());
            String upToTheComparison = body(each.before(), "true", "");
            BytesClassLoader loader = new BytesClassLoader(Compiler.compile(source(Map.of(
                    "reaches", upToTheComparison, "m", whole))), getClass().getClassLoader());
            List<List<Long>> gets = rowsThatFinish(loader, "reaches");
            List<List<Long>> completes = rowsThatFinish(loader, "m");
            if (!gets.equals(rowsWhere(each.gets())) || !completes.equals(rowsWhere(
                    each.completes()))) {
                wrong.add(each.name() + ": the oracle is not the rows the program stops at: gets "
                        + gets + ", completes " + completes);
                continue;
            }
            Compilation read = measured(source(Map.of("m", whole)), Adequacy.Level.WITNESS);
            String report = report(read);
            if (nothingArrives(report) != gets.isEmpty()) {
                wrong.add(each.name() + ": " + (gets.isEmpty() ? "no row" : "a row")
                        + " gets to the comparison, and the report says "
                        + (gets.isEmpty() ? "otherwise" : "none does") + "\n" + report);
            }
            if (somethingIsNotRead(report) != each.unread()) {
                wrong.add(each.name() + ": " + (each.unread() ? "read" : "not read") + "\n"
                        + report);
            }
            // What may stop a run in the comparison is a row that gets to it and does not complete.
            if (!each.unread() && !gets.isEmpty()
                    && mayStop(report) != !completes.equals(gets)) {
                wrong.add(each.name() + ": a run that gets to the comparison "
                        + (completes.equals(gets) ? "always" : "does not always") + " completes"
                        + " it, and the report says otherwise\n" + report);
            }
            if (each.asItsOwn()) {
                List<String> alone = linesOf(measured(source(Map.of("m",
                        body("", each.comparison(), ""))), Adequacy.Level.WITNESS));
                if (!alone.equals(linesOf(read))) {
                    wrong.add(each.name() + ": the comparison draws " + linesOf(read)
                            + " and alone draws " + alone);
                }
            }
        }
        assertEquals(List.of(), wrong);
    }

    /**
     * Every row the comparison is owed is a row that gets to it, run: the rows are composed by
     * what the analysis says reaches the comparison, and the program is what says whether they do.
     */
    @Test
    void everyRowOwedAtTheComparisonGetsToItAndCompletesIt() throws Exception {
        List<String> wrong = new ArrayList<>();
        int owed = 0;
        for (Case each : CASES) {
            String whole = body(each.before(), each.comparison(), each.after());
            BytesClassLoader loader = new BytesClassLoader(Compiler.compile(source(Map.of(
                    "reaches", body(each.before(), "true", ""), "m", whole))),
                    getClass().getClassLoader());
            Object reaches = Emitted.behavior(loader, MODULE, "reaches").getConstructor()
                    .newInstance();
            Object completes = Emitted.behavior(loader, MODULE, "m").getConstructor()
                    .newInstance();
            Compilation compilation = measured(source(Map.of("m", whole)), Adequacy.Level.ALL);
            List<BorderAssessment> lines = Adequacy.readingsOf(compilation.db(), MODULE).get("m");
            for (BorderAssessment border : lines == null ? List.<BorderAssessment>of() : lines) {
                for (ItemAssessment item : border.items().values()) {
                    if (!(item instanceof ItemAssessment.Owed given)) {
                        continue;
                    }
                    for (ItemAssessment.Attempt attempt : given.searches().each()) {
                        if (!(attempt instanceof ItemAssessment.Attempt.Certified certified)) {
                            continue;
                        }
                        owed++;
                        String row = certified.row().inputs().getFirst().text();
                        Matcher fields = ROW.matcher(row);
                        if (!fields.matches()) {
                            wrong.add(each.name() + ": a row is not written as " + ROW + ": "
                                    + row);
                            continue;
                        }
                        long x = Long.parseLong(fields.group(1));
                        long k = Long.parseLong(fields.group(2));
                        if (!finishes(loader, reaches, x, k)) {
                            wrong.add(each.name() + ": " + row + " is owed and gets to no"
                                    + " comparison");
                        } else if (!finishes(loader, completes, x, k)) {
                            wrong.add(each.name() + ": " + row + " is owed and stops in the"
                                    + " comparison");
                        }
                    }
                }
            }
        }
        assertEquals(List.of(), wrong);
        assertTrue(owed > 0, "no row was owed");
    }

    /** A row as the report writes it. */
    private static final Pattern ROW = Pattern.compile("Pair \\{ x = (-?\\d+), k = (-?\\d+) }");

    private static String guarded(String hole, String relation) {
        return DECLARED + """

                behavior m : (p: Pair) -> Ok | No | Skipped
                let m (p) = {
                    guard p.x /= %s else Skipped
                    guard %s else No
                    Ok
                }
                """.formatted(hole, relation);
    }

    /** The places the report says the comparison leaves undivided. */
    private static Set<String> undivided(String report) {
        Set<String> places = new TreeSet<>();
        report.lines().filter(line -> line.contains("no line:")
                        && line.contains("rather than dividing"))
                .forEach(line -> places.add(line.replaceAll(".*about `([^`]*)`.*", "$1")));
        return places;
    }

    /** What running {@code m} on a row comes to, as the case it answers. */
    private static String answer(BytesClassLoader loader, Object behavior, long x, long k)
            throws Exception {
        Object row = Codecs.decoded(loader, MODULE + ".Pair", Map.of("x", x, "k", k));
        return Codecs.apply(behavior, row).getClass().getSimpleName();
    }

    /**
     * A place is left undivided only where no value of it settles the comparison: among the rows
     * that get to it, the other values come out both ways beside each value of the place. Held to
     * the runs: the answers of the rows are what they are, and a value of {@code k} every row at
     * which comes out one way is one the report may not leave {@code k} undivided past.
     *
     * <p>A value held away from a number is no end of what the number takes, so for an order the
     * other side still takes values on both sides of every value asked of it, and each place is
     * left undivided and nothing is unread; for an equation no value of the other side is the one
     * held away, so that value of the other place settles the relation, and only the held place is
     * left undivided.
     */
    @Test
    void aValueHeldAwayFromANumberLeavesAPlaceUndividedOnlyWhereTheRunsComeOutBothWays()
            throws Exception {
        List<String> wrong = new ArrayList<>();
        for (String relation : List.of("p.x >= p.k", "p.x < p.k", "p.x == p.k", "p.x /= p.k")) {
            String source = guarded("0", relation);
            BytesClassLoader loader =
                    new BytesClassLoader(Compiler.compile(source), getClass().getClassLoader());
            Object behavior = Emitted.behavior(loader, MODULE, "m").getConstructor().newInstance();
            Set<String> settledX = new TreeSet<>();
            Set<String> settledK = new TreeSet<>();
            // The values the grid has others on both sides of. A value at the end of the grid is
            // one nothing of the grid is past, and the ends of the type are not values a model
            // divides.
            for (long fixed : INSIDE) {
                Set<String> byX = new TreeSet<>();
                Set<String> byK = new TreeSet<>();
                for (long other : VALUES) {
                    String atX = answer(loader, behavior, fixed, other);
                    String atK = answer(loader, behavior, other, fixed);
                    if (!atX.equals("Skipped")) {
                        byX.add(atX);
                    }
                    if (!atK.equals("Skipped")) {
                        byK.add(atK);
                    }
                }
                if (byX.size() == 1) {
                    settledX.add("x=" + fixed);
                }
                if (byK.size() == 1) {
                    settledK.add("k=" + fixed);
                }
            }
            String report = report(measured(source, Adequacy.Level.WITNESS));
            Set<String> claimed = undivided(report);
            if (somethingIsNotRead(report)) {
                wrong.add(relation + " is not read\n" + report);
            }
            // The grid holds both signs and the ends, so a place that is settled at any of its
            // values is one a claim of undivided is wrong about.
            if (claimed.contains("p.x") && !settledX.isEmpty()) {
                wrong.add(relation + ": p.x is left undivided and the runs settle " + settledX);
            }
            if (claimed.contains("p.k") && !settledK.isEmpty()) {
                wrong.add(relation + ": p.k is left undivided and the runs settle " + settledK);
            }
            // And where the runs settle no value of a place, an order says so.
            boolean anOrder = relation.contains("<") || relation.contains(">");
            if (anOrder && !claimed.equals(Set.of("p.k", "p.x"))) {
                wrong.add(relation + ": the runs settle no value, and the places left undivided"
                        + " are " + claimed);
            }
            if (!anOrder && !settledK.isEmpty() && claimed.contains("p.k")) {
                wrong.add(relation + ": nought settles it for k");
            }
        }
        assertEquals(List.of(), wrong);
        assertFalse(CASES.isEmpty());
    }
}
