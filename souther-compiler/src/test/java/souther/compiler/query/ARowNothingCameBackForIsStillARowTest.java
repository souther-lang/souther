package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Prepared;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.RowOutcome;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row nothing came back for is listed as a row, with the reason from where it is written.
 *
 * <p>What a module wrote and what a reading of it came back with are two sets, and only the first
 * is the model. A reading can stop short of a whole block — the classes it would run will not link,
 * which the language accepts rather than refuses — and the rows in it then have no outcome at all.
 * Listed as what came back, those rows are rows nothing downstream would ever hear of, and the
 * behavior reads as having said nothing about an input that is written down in front of it.
 *
 * <p>So a source's rows and what became of reading that source are put together while both are
 * still that source's. A behavior may be exampled in its own module and in an attached file, and
 * what stopped a reading of one says nothing about the other; matched after the two are gathered
 * under the behavior's name, a row takes whichever reason was recorded first and is told about a
 * file it is not in.
 */
class ARowNothingCameBackForIsStillARowTest {

    private static final String MODULE = """
            module demo

            data Amount = Int
            data Receipt = { total: Amount }

            behavior billFor : (a: Amount) -> Receipt constructs Receipt

            let billFor (a) = Receipt { total = a }

            example billFor
                | "one" : (Amount(1)) -> Receipt { total = Amount(1) }
                | "two" : (Amount(2)) -> Receipt { total = Amount(2) }
            """;

    /** The same behavior exampled where its rows outgrew the model. */
    private static final String BESIDE = """
            examples for demo

            example billFor
                | "beside" : (Amount(3)) -> Receipt { total = Amount(3) }
            """;

    @Test
    void aRowNothingCameBackForIsListedWithWhyNothingDid() {
        Read read = read(List.of(MODULE));
        List<RowOutcome> ran = read.ran("billFor");
        assertEquals(2, ran.size(), () -> "the module's rows came back as " + ran);

        // A reading that stopped: the second row's outcome is not there, and the reading says why.
        // What a block that would not link leaves is exactly this.
        List<Output.RowsRead.ReadRow> rows = read.rowsOf(read.sources().getFirst(),
                List.of(ran.get(0)),
                List.of(Incompleteness.at(Incompleteness.Code.LINKAGE_FAILED,
                        Incompleteness.Scope.BEHAVIOR, "billFor", ran.get(1).at())))
                .get("billFor");

        assertEquals(2, rows.size(), () -> "both written rows are listed: " + rows);
        assertInstanceOf(Output.RowsRead.ReadRow.Ran.class, rows.get(0));
        Output.RowsRead.ReadRow.NotRun missing =
                assertInstanceOf(Output.RowsRead.ReadRow.NotRun.class, rows.get(1));
        assertEquals(ran.get(1).identity(), missing.identity(),
                "and the one nothing came back for says which row it is");
        assertEquals(Incompleteness.Code.LINKAGE_FAILED, missing.why(),
                "and why nothing came back for it");
    }

    /** Where nothing was observed of the source at all, that is what each of its rows says. */
    @Test
    void andWhereNothingWasObservedOfTheSourceEveryRowSaysThat() {
        Read read = read(List.of(MODULE));

        List<Output.RowsRead.ReadRow> rows =
                read.rowsOf(read.sources().getFirst(), null, List.of()).get("billFor");

        assertEquals(2, rows.size(), () -> "both written rows are listed: " + rows);
        for (Output.RowsRead.ReadRow row : rows) {
            assertEquals(Incompleteness.Code.OBSERVATION_ABSENT,
                    assertInstanceOf(Output.RowsRead.ReadRow.NotRun.class, row).why());
        }
    }

    /**
     * A row takes the reason of the source it is written in, and not one from beside it.
     *
     * <p>Two sources exampling one behavior, each stopping its own way. Read after the two are
     * gathered under the behavior's name, the rows of both take whichever reason came first — and
     * a reader is told about a file the row is not in.
     */
    @Test
    void andARowTakesTheReasonOfTheSourceItIsWrittenIn() {
        Read read = read(List.of(MODULE, BESIDE));
        List<SourceId> sources = read.sources();
        assertEquals(2, sources.size(), () -> "the module's rows are written in " + sources);

        // The model's own source could not link; the attached file was not observed at all.
        Map<String, List<Output.RowsRead.ReadRow>> rows = new LinkedHashMap<>();
        Set<String> named = new LinkedHashSet<>();
        Output.RowsRead.readOneSource(read.prepared, sources.get(0),
                read.observationSaying(List.of(),
                        List.of(Incompleteness.at(Incompleteness.Code.LINKAGE_FAILED,
                                Incompleteness.Scope.BEHAVIOR, "billFor",
                                read.ran("billFor").getFirst().at()))),
                rows, named);
        Output.RowsRead.readOneSource(read.prepared, sources.get(1), null, rows, named);

        List<Incompleteness.Code> why = new ArrayList<>();
        for (Output.RowsRead.ReadRow row : rows.get("billFor")) {
            why.add(assertInstanceOf(Output.RowsRead.ReadRow.NotRun.class, row).why());
        }
        assertEquals(List.of(Incompleteness.Code.LINKAGE_FAILED, Incompleteness.Code.LINKAGE_FAILED,
                        Incompleteness.Code.OBSERVATION_ABSENT),
                why, "each row says what happened where it is written");
    }

    /**
     * A row with neither an outcome nor a reason is this compiler having lost one.
     *
     * <p>Not a state to describe. A reading is short of a row only for a reason it recorded, so
     * meeting one with neither is the invariant this whole reading exists for being broken — and
     * answering it with a reason of our own would put the row back among the ones nothing says
     * anything about, which is where it was.
     */
    @Test
    void andARowWithNeitherAnOutcomeNorAReasonIsRefused() {
        Read read = read(List.of(MODULE));

        IllegalStateException lost = assertThrows(IllegalStateException.class,
                () -> read.rowsOf(read.sources().getFirst(), List.of(), List.of()));
        assertTrue(lost.getMessage().contains("nothing there says why"),
                () -> "what it says is: " + lost.getMessage());
    }

    /** A compilation, and the pieces a reading of its rows is made from. */
    private record Read(Answer<Prepared> prepared, Db db, String module) {

        List<SourceId> sources() {
            return new ArrayList<>(db.ask(new Front.ExampleSources(module)).value());
        }

        List<RowOutcome> ran(String behavior) {
            Output.RowsRead.Of read = db.ask(new Output.RowsRead(module)).value();
            return new ArrayList<>(read.byBehavior().get(behavior).ran());
        }

        /** One source's rows, read against an observation that says {@code rows} and {@code gaps}. */
        Map<String, List<Output.RowsRead.ReadRow>> rowsOf(SourceId source, List<RowOutcome> rows,
                                                          List<Incompleteness> gaps) {
            Map<String, List<Output.RowsRead.ReadRow>> out = new LinkedHashMap<>();
            Output.RowsRead.readOneSource(prepared, source,
                    rows == null ? null : observationSaying(rows, gaps), out, new LinkedHashSet<>());
            return out;
        }

        Output.Examples.Of observationSaying(List<RowOutcome> rows, List<Incompleteness> gaps) {
            return new Output.Examples.Of(rows, gaps);
        }
    }

    private static Read read(List<String> sources) {
        Compilation compilation = Compilation.ofSources(sources, ModulePath.EMPTY);
        Acceptance.of(compilation);
        Db db = compilation.db();
        return new Read(db.ask(new Shapes.Prepared("demo")), db, "demo");
    }
}
