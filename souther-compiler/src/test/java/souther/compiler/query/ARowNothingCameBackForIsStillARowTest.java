package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Prepared;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.RowOutcome;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row nothing came back for is listed as a row all the same.
 *
 * <p>What a module wrote and what a reading of it came back with are two sets, and only the first
 * is the model. A reading can stop short of a whole block — the classes it would run will not link,
 * which the language accepts rather than refuses — and the rows in it then have no outcome at all.
 * Listed as what came back, those rows are rows nothing downstream would ever hear of, and the
 * behavior reads as having said nothing about an input that is written down in front of it.
 *
 * <p>So the gathering is over what was written, and what came back is attached to it. Asked here of
 * a reading with an outcome taken out of it, because that is the shape a reading that stopped
 * leaves and it is not otherwise reachable from a program the language accepts.
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

    @Test
    void aRowNothingCameBackForIsListedWithWhyNothingDid() {
        Compilation compilation = Compilation.ofSources(List.of(MODULE), ModulePath.EMPTY);
        Acceptance.of(compilation);
        Db db = compilation.db();
        Answer<Prepared> prepared = db.ask(new Shapes.Prepared("demo"));
        List<RowOutcome> ran = ranRows(db);
        assertEquals(2, ran.size(), () -> "the module's rows came back as " + ran);

        // A reading that stopped: the second row's outcome is not there. What a block that would
        // not link leaves is exactly this — the rows are written, and nothing came back for them.
        Map<String, List<RowOutcome>> short0 = new LinkedHashMap<>();
        short0.put("billFor", List.of(ran.get(0)));
        Map<String, List<Incompleteness>> stopped = new LinkedHashMap<>();
        stopped.put("billFor", List.of(Incompleteness.at(Incompleteness.Code.LINKAGE_FAILED,
                Incompleteness.Scope.BEHAVIOR, "billFor", ran.get(1).at())));

        List<Output.RowsRead.ReadRow> rows = Output.RowsRead
                .writtenRows(prepared, short0, List.of(), stopped)
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

    /** And where a whole source went unobserved, the reason larger than the behavior is the one
     *  each of its rows takes. */
    @Test
    void andWhereTheWholeReadingStoppedEveryRowTakesThatReason() {
        Compilation compilation = Compilation.ofSources(List.of(MODULE), ModulePath.EMPTY);
        Acceptance.of(compilation);
        Db db = compilation.db();
        Answer<Prepared> prepared = db.ask(new Shapes.Prepared("demo"));

        List<Output.RowsRead.ReadRow> rows = Output.RowsRead
                .writtenRows(prepared, Map.of(),
                        List.of(Incompleteness.ofSource(Incompleteness.Code.OBSERVATION_ABSENT,
                                sourceOf(db))),
                        Map.of())
                .get("billFor");

        assertEquals(2, rows.size(), () -> "both written rows are listed: " + rows);
        for (Output.RowsRead.ReadRow row : rows) {
            assertEquals(Incompleteness.Code.OBSERVATION_ABSENT,
                    assertInstanceOf(Output.RowsRead.ReadRow.NotRun.class, row).why());
        }
    }

    private static List<RowOutcome> ranRows(Db db) {
        Output.RowsRead.Of read = db.ask(new Output.RowsRead("demo")).value();
        List<RowOutcome> out = new ArrayList<>(read.byBehavior().get("billFor").ran());
        assertTrue(!out.isEmpty(), "the module's rows ran");
        return out;
    }

    private static souther.compiler.source.SourceId sourceOf(Db db) {
        return db.ask(new Front.ExampleSources("demo")).value().getFirst();
    }
}
