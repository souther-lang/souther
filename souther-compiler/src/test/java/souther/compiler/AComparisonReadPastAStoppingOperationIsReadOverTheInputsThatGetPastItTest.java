package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.BiPredicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A comparison read past an operation that stops a run is read over the inputs that get past it,
 * held against the runs themselves.
 *
 * <p>Each model works out something that stops a run on some inputs and compares after it. Which
 * rows get to the comparison is found by running the compiled behavior on a grid of rows and
 * seeing which stop, and not by anything the analysis reads. The analysis is then held to that:
 * a comparison some row gets to is never said to have no row arrive at it, one no row gets to is,
 * and what the report leaves unread is what the operation's own account does not say where it
 * answers.
 */
class AComparisonReadPastAStoppingOperationIsReadOverTheInputsThatGetPastItTest {

    private static final String MODULE = "probe.stop";

    private static final String DECLARED = """
            module probe.stop

            data Ok
            data No

            data Pair = { x: Int, k: Int }
            """;

    private static final long GREATEST = Long.MAX_VALUE;

    /** The values of each field a row of the grid takes, beside the greatest {@code Int}, which
     *  a sum past it stops at. */
    private static final long[] VALUES = {-3, -2, -1, 0, 1, 2, 3, GREATEST};

    /**
     * One model: what is worked out before the comparison, the comparison, and where the run
     * stops by the language's own account, written out of the row.
     */
    private record Case(String name, String before, String comparison,
                        BiPredicate<Long, Long> stops, boolean unread) {}

    private static String body(String before, String comparison) {
        return """

                behavior m : (p: Pair) -> Bool
                let m (p) = {
                    %s
                    %s
                }
                """.formatted(before, comparison);
    }

    private static final String QUOTIENT = "let y = Rational.toInt(DOWN, 1 / %s)";

    private static final List<Case> CASES = List.of(
            new Case("a quotient by x, then x and k related",
                    QUOTIENT.formatted("p.x"), "p.x + 1 >= p.k",
                    (x, k) -> x == 0 || x == GREATEST, false),
            new Case("a quotient by x, then k alone",
                    QUOTIENT.formatted("p.x"), "p.k >= 5",
                    (x, k) -> x == 0, false),
            new Case("a quotient by x, then x alone",
                    QUOTIENT.formatted("p.x"), "p.x + 1 >= 5",
                    (x, k) -> x == 0 || x == GREATEST, false),
            new Case("a quotient by k, then x alone",
                    QUOTIENT.formatted("p.k"), "p.x + 1 >= 5",
                    (x, k) -> k == 0 || x == GREATEST, false),
            new Case("a quotient by nought, then x and k related",
                    QUOTIENT.formatted("0"), "p.x + 1 >= p.k",
                    (x, k) -> true, false),
            new Case("a quotient by what is not stated, then x and k related",
                    QUOTIENT.formatted("(if p.x > 0 then p.x else 0)"), "p.x + 1 >= p.k",
                    (x, k) -> x <= 0 || x == GREATEST, true));

    private static String report(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** Whether the report says no row that arrives at some comparison holds a value at its line. */
    private static boolean nothingArrives(String report) {
        return report.contains("no row that arrives at it");
    }

    private static boolean somethingIsNotRead(String report) {
        return report.contains("not read:");
    }

    /** The rows of the grid a run of {@code m} gets to the end of. */
    private static List<List<Long>> rowsThatGetPast(String source) throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(source), Case.class.getClassLoader());
        Object behavior = Emitted.behavior(loader, MODULE, "m").getConstructor().newInstance();
        List<List<Long>> past = new ArrayList<>();
        for (long x : VALUES) {
            for (long k : VALUES) {
                Object row = Codecs.decoded(loader, MODULE + ".Pair", Map.of("x", x, "k", k));
                try {
                    Codecs.apply(behavior, row);
                    past.add(List.of(x, k));
                } catch (RuntimeException stopped) {
                    // A run that stops gets no further.
                }
            }
        }
        return past;
    }

    private static List<List<Long>> rowsWhereTheRunDoesNotStop(BiPredicate<Long, Long> stops) {
        List<List<Long>> rows = new ArrayList<>();
        for (long x : VALUES) {
            for (long k : VALUES) {
                if (!stops.test(x, k)) {
                    rows.add(List.of(x, k));
                }
            }
        }
        return rows;
    }

    /**
     * What the language says stops a run is what runs stop at, so that the grid is an oracle of
     * which rows get to the comparison; and the report is held to it.
     */
    @Test
    void theReportIsHeldToTheRowsThatGetToTheComparison() throws Exception {
        List<String> wrong = new ArrayList<>();
        for (Case each : CASES) {
            String source = DECLARED + body(each.before(), each.comparison());
            List<List<Long>> past = rowsThatGetPast(source);
            if (!past.equals(rowsWhereTheRunDoesNotStop(each.stops()))) {
                wrong.add(each.name() + ": the oracle is not the rows the program stops at: "
                        + past);
                continue;
            }
            String report = report(source);
            if (!past.isEmpty() && nothingArrives(report)) {
                wrong.add(each.name() + ": a row gets to the comparison, and the report says"
                        + " none does\n" + report);
            }
            if (past.isEmpty() && !nothingArrives(report)) {
                wrong.add(each.name() + ": no row gets to the comparison, and the report does"
                        + " not say so\n" + report);
            }
            if (somethingIsNotRead(report) != each.unread()) {
                wrong.add(each.name() + ": " + (each.unread() ? "read" : "not read") + "\n"
                        + report);
            }
        }
        assertEquals(List.of(), wrong);
    }

    private static String guarded(String hole, String relation) {
        return DECLARED + """

                behavior m : (p: Pair) -> Ok | No
                let m (p) = {
                    guard p.x /= %s else No
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

    /**
     * A value an operation before the comparison holds a number away from is no end of what the
     * number takes, so for an order the other side still takes values on both sides of every value
     * asked of it: each place is left undivided, and nothing is unread. For an equality it does
     * not: no value of the other side is the one held away, so that value of the other place
     * settles the relation on its own, and only the held place is left undivided.
     */
    @Test
    void aValueHeldAwayFromANumberLeavesAnOrderUndividedAndAnEquationDividedByIt() {
        for (String hole : List.of("0", "5", "-2")) {
            for (String order : List.of("p.x >= p.k", "p.x < p.k", "p.x <= p.k", "p.x > p.k")) {
                String report = report(guarded(hole, order));
                assertFalse(somethingIsNotRead(report), hole + " " + order + "\n" + report);
                assertEquals(Set.of("p.k", "p.x"), undivided(report), hole + " " + order);
            }
            for (String equation : List.of("p.x == p.k", "p.x /= p.k")) {
                String report = report(guarded(hole, equation));
                assertFalse(somethingIsNotRead(report), hole + " " + equation + "\n" + report);
                assertEquals(Set.of("p.x"), undivided(report), hole + " " + equation);
            }
        }
    }
}
