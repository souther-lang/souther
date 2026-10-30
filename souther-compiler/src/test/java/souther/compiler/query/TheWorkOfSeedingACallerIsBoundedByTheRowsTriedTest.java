package souther.compiler.query;

import souther.compiler.check.AnalysisBody;
import souther.compiler.inputs.InputReading;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.partition.MeasuredInput;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Rows of callees are tried up to a limit, taken or refused, and a value tried twice is built once.
 */
class TheWorkOfSeedingACallerIsBoundedByTheRowsTriedTest {

    private static final int ROWS = 12;

    private static String model(boolean distinct) {
        StringBuilder rows = new StringBuilder();
        for (int i = 1; i <= ROWS; i++) {
            rows.append("    | (").append(distinct ? i : 1).append(") -> 0\n");
        }
        return """
                module repro.bound

                behavior f : (n: Int) -> Int

                let f (n) = n

                example f
                """ + rows + """

                behavior g : (xs: List<Int>) -> Int

                let g (xs) = List.fold((acc, x) -> acc + f(x), 0, xs)
                """;
    }

    /** How many values the decoder is asked about, and what is offered, of {@code g}. */
    private record Seeded(int built, List<Generator.GeneratedRow> rows) {}

    private static Seeded seeded(String source, boolean refuseAll, int limit) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Db db = compilation.db();
        var surface = db.ask(new Shapes.CheckSurface("repro.bound")).value();
        var behavior = Adequacy.specOf(surface, "g");
        InputReading input = Adequacy.inputReadingOf(db, "repro.bound", behavior);
        AnalysisBody analysis = db.ask(new Bodies.Observable("repro.bound")).value()
                .analysisBodies().get("g");
        MeasuredInput subject = Adequacy.subjectOf(db, "repro.bound", behavior, input);
        AtomicInteger built = new AtomicInteger();
        Generator.CandidateCheck check = (_, _) -> {
            built.incrementAndGet();
            return refuseAll ? new Generator.CandidateCheck.Built.Refused("no")
                    : new Generator.CandidateCheck.Built.NothingBuiltIt();
        };
        List<Generator.GeneratedRow> rows = CallExampleSeeds.rowsFor(db, "repro.bound",
                subject, input, analysis, check, List.of(), true, limit);
        return new Seeded(built.get(), rows);
    }

    @Test
    void refusedRowsCostAsMuchAsTakenOnesAndStopAtTheLimit() {
        Seeded refused = seeded(model(true), true, 5);
        assertEquals(List.of(), refused.rows());
        assertEquals(5, refused.built(), "the decoder is asked about the rows tried and no more");
    }

    @Test
    void takenRowsStopAtTheLimitToo() {
        Seeded taken = seeded(model(true), false, 5);
        assertEquals(5, taken.rows().size());
        assertEquals(5, taken.built());
    }

    @Test
    void aCallWrittenTwiceIsTriedOnce() {
        String twice = """
                module repro.bound

                behavior f : (n: Int) -> Int

                let f (n) = n

                example f
                    | (1) -> 1
                    | (2) -> 2
                    | (3) -> 3

                behavior h : (n: Int) -> Int

                let h (n) = n

                example h
                    | (100) -> 100
                    | (101) -> 101

                behavior g : (xs: List<Int>) -> Int

                let g (xs) = List.fold((acc, x) -> acc + f(x) + f(x) + h(x), 0, xs)
                """;
        Seeded seeded = seeded(twice, false, 5);
        assertTrue(seeded.rows().stream().anyMatch(row -> row.inputs().getFirst().text()
                        .equals("[100]")),
                () -> "f's three rows and h's first are tried within five: " + seeded.rows());
    }

    @Test
    void aRowTheCallerHasWrittenTakesNoneOfTheRowsTried() {
        StringBuilder f = new StringBuilder();
        StringBuilder g = new StringBuilder();
        for (int i = 1; i <= 8; i++) {
            f.append("    | (").append(i).append(") -> ").append(i).append('\n');
            if (i <= 5) {
                g.append("    | ([").append(i).append("]) -> ").append(i).append('\n');
            }
        }
        String written = """
                module repro.bound

                behavior f : (n: Int) -> Int

                let f (n) = n

                example f
                """ + f + """

                behavior g : (xs: List<Int>) -> Int

                let g (xs) = List.fold((acc, x) -> acc + f(x), 0, xs)

                example g
                """ + g;
        Seeded seeded = seeded(written, false, 5);
        assertEquals(List.of("[6]", "[7]", "[8]"), seeded.rows().stream()
                .map(row -> row.inputs().getFirst().text()).toList());
        assertEquals(3, seeded.built(), "the five written rows are not built");
    }

    @Test
    void aWrittenRowLiftedToTwiceTakesNoneOfTheRowsTriedOnlyTheFirstTime() {
        String source = """
                module repro.bound

                behavior f : (n: Int) -> Int

                let f (n) = n

                example f
                    | (1) -> 1
                    | (2) -> 2

                behavior h : (n: Int) -> Int

                let h (n) = n

                example h
                    | (1) -> 1
                    | (3) -> 3

                behavior g : (xs: List<Int>) -> Int

                let g (xs) = List.fold((acc, x) -> acc + f(x) + h(x), 0, xs)

                example g
                    | ([1]) -> 2
                """;
        assertEquals(List.of("[2]"), seeded(source, false, 2).rows().stream()
                .map(row -> row.inputs().getFirst().text()).toList(),
                "the second lift to the written [1] is a row tried, and is not offered");
        assertEquals(List.of("[2]", "[3]"), seeded(source, false, 3).rows().stream()
                .map(row -> row.inputs().getFirst().text()).toList());
    }

    @Test
    void aValueTriedTwiceIsBuiltOnce() {
        Seeded same = seeded(model(false), false, ROWS);
        assertEquals(1, same.rows().size());
        assertEquals(1, same.built());
        assertTrue(same.rows().getFirst().inputs().stream().map(FixtureTemplate::text)
                .allMatch(text -> text.equals("[1]")));
    }
}
