package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.report.AdequacyReport;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What measures a run reads the elaboration the classes it ran came from.
 *
 * <p>A plan is an index onto the bodies of one elaboration, so a partial image and a whole check are
 * two coordinate systems whatever the module is called. A measure that took its numbering from the
 * whole check would read a run against numbers nothing wrote, and would put the structure of a
 * program that did not run beside the observation of the one that did.
 *
 * <p>So the measuring side asks {@link Bodies.Observable} and never {@link Bodies.Checked}. Held as
 * a rule over the sources rather than one call site at a time: what went wrong was one reader among
 * many asking the wrong question, and a list of the ones that were noticed is not the population.
 *
 * <p><b>Directly, and not through what it reaches.</b> {@code Observable} answers with the whole
 * check's own elaboration where every implementation of the module may be run, which is what keeps
 * one program from being two. Forbidding the reach would forbid that.
 */
class ARunIsMeasuredInTheElaborationThatProducedItsClassesTest {

    /** Where the measuring side is written. */
    private static final List<Path> MEASURES = List.of(
            Path.of("src/main/java/souther/compiler/query/Adequacy.java"),
            Path.of("src/main/java/souther/compiler/report/AdequacyReport.java"));

    /** What asking for the whole module's elaboration looks like in either of them. */
    private static final List<String> ASKING_FOR_THE_WHOLE_CHECK =
            List.of("new Bodies.Checked(", "new Checked(");

    @Test
    void nothingThatMeasuresARunAsksForTheWholeModulesCheck() throws IOException {
        List<String> found = new ArrayList<>();
        for (Path each : MEASURES) {
            List<String> lines = Files.readAllLines(each);
            for (int i = 0; i < lines.size(); i++) {
                String line = lines.get(i);
                if (ASKING_FOR_THE_WHOLE_CHECK.stream().anyMatch(line::contains)) {
                    found.add(each.getFileName() + ":" + (i + 1) + " " + line.strip());
                }
            }
        }

        assertEquals(List.of(), found,
                "a measure of a run asking for the elaboration a jar is made from. A run is"
                        + " measured in the elaboration that produced the classes it ran, which is"
                        + " `Bodies.Observable`; the whole check is what publication reads");
    }

    /** And the sources it reads are the ones that are there. */
    @Test
    void theSourcesThisReadsAreThere() {
        List<Path> missing = MEASURES.stream().filter(each -> !Files.isRegularFile(each)).toList();

        assertEquals(List.of(), missing,
                "this holds a rule over sources named by path, so a file that moved leaves it"
                        + " holding nothing and saying so");
    }

    /**
     * A module whose own bodies check, whose closure is partial, and which has rows.
     *
     * <p>The three together are what it takes: {@code calls} reaches an implementation the module it
     * imports could not make, so this module is observed against less than it checks, and
     * {@code apart} has a row that runs. Read against the whole check's numbering, the run comes
     * back under a numbering nothing wrote.
     */
    private static final String DOWN = """
            module probe.down exposing ( Seat, twice )

            data Seat = Int
                invariant value >= 1 && value <= 300

            behavior twice : (n: Int) -> Seat
            let twice (n) = mint(n)

            behavior mint : (n: Int) -> Seat
                constructs Seat
            let mint (n) = Seat(0)
            """;

    private static final String UP = """
            module probe.up

            import probe.down ( Seat, twice )

            behavior calls : (n: Int) -> Seat
            let calls (n) = twice(n)

            behavior apart : (n: Int) -> Int
            let apart (n) = n

            example apart
                | "one" : (1) -> 1
            """;

    /**
     * And the run of such a module is read, and its row measured.
     *
     * <p>The rule above is held over the sources; this is held over a model. A reader that took the
     * whole check's numbering does not fail an assertion here — it throws where the two numberings
     * are aligned, which is what this model met before the rule was applied.
     */
    @Test
    void aModuleObservedAgainstLessThanItChecksIsStillRead() {
        Compilation compilation = Compilation.ofSources(List.of(DOWN, UP),
                souther.compiler.meta.ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        assertEquals(List.of("apart"),
                new ArrayList<>(compilation.db().ask(new Bodies.Observable("probe.up"))
                        .value().emits()),
                "this module is written to be observed against one of its two implementations");
        assertEquals(1, compilation.db().ask(new Output.RowsRead("probe.up")).value()
                        .byBehavior().get("apart").ran().size(),
                "and the one it may run has a row that ran");

        AdequacyReport report = AdequacyReport.of(compilation);
        assertEquals(List.of("apart"), Stream.of(report)
                        .flatMap(it -> it.findings().stream())
                        .map(it -> it.subject().toString())
                        .filter(it -> it.contains("apart"))
                        .map(_ -> "apart")
                        .distinct()
                        .toList(),
                () -> "the row's own behavior is measured and something is said about it: "
                        + report.findings());
    }
}
