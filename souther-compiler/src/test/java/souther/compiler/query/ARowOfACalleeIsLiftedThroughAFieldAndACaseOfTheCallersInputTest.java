package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.check.AnalysisBody;
import souther.compiler.inputs.InputReading;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.partition.MeasuredInput;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row of a callee is lifted through an argument that stands at a field of the caller's input, or
 * at a value narrowed by {@code as}, into the record and the case the model builds around it.
 */
class ARowOfACalleeIsLiftedThroughAFieldAndACaseOfTheCallersInputTest {

    private static final String CALLEES = """
            behavior isFifty : (n: Int) -> Bool
            let isFifty (n) = n == 50
            example isFifty
                | (50) -> true
                | (51) -> false
            behavior same : (x: Int, y: Int) -> Bool
            let same (x, y) = x == y
            example same
                | (1, 1) -> true
                | (1, 2) -> false
            """;

    private static final String A_FIELD = """
            module repro.lift
            data S = { score: Int }
            behavior f : (s: S) -> Bool
            let f (s) = isFifty(s.score)
            """ + CALLEES;

    private static final String A_CASE = """
            module repro.lift
            data Playing = { score: Int }
            data State = Playing | Out
            behavior f : (s: State) -> Bool
            let f (s) =
                match s with
                    | Out -> false
                    | Playing as p -> isFifty(p.score)
            """ + CALLEES;

    private static final String TWO_FIELDS = """
            module repro.lift
            data P = { a: Int, b: Int }
            behavior f : (p: P) -> Bool
            let f (p) = same(p.a, p.b)
            """ + CALLEES;

    private static final String ONE_FIELD_TWICE = """
            module repro.lift
            data P = { a: Int, b: Int }
            behavior f : (p: P) -> Bool
            let f (p) = same(p.a, p.a)
            """ + CALLEES;

    private static final String A_COMPUTED_ARGUMENT = """
            module repro.lift
            data S = { score: Int }
            behavior f : (s: S) -> Bool
            let f (s) = isFifty(s.score + 1)
            """ + CALLEES;

    @Test
    void anArgumentAtAFieldIsHandedTheRecordHoldingTheValue() {
        List<String> rows = seededInputs(A_FIELD);
        assertTrue(rows.contains("[S { score = 50 }]"), () -> "the row (50) is lifted: " + rows);
        assertTrue(rows.contains("[S { score = 51 }]"), () -> "the row (51) is lifted: " + rows);
    }

    @Test
    void anArgumentAtAFieldOfACaseIsHandedTheCase() {
        List<String> rows = seededInputs(A_CASE);
        assertTrue(rows.contains("[Playing { score = 50 }]"),
                () -> "the case the argument is read under is built: " + rows);
    }

    @Test
    void twoArgumentsAtTwoFieldsAreHandedOneRecord() {
        List<String> rows = seededInputs(TWO_FIELDS);
        assertTrue(rows.contains("[P { a = 1, b = 2 }]"),
                () -> "both fields are put in the one record: " + rows);
    }

    @Test
    void oneFieldGivenTwoValuesIsNoRow() {
        List<String> rows = seededInputs(ONE_FIELD_TWICE);
        assertEquals(List.of("[P { a = 1, b = 0 }]"), rows,
                "the row giving the field two values lifts to nothing; the other fixes the field "
                        + "and leaves the rest of the record to the model");
    }

    @Test
    void anArgumentComputedFromAFieldIsNoRow() {
        assertEquals(List.of(), seededInputs(A_COMPUTED_ARGUMENT));
    }

    /** The inputs, written, of each row {@code f} is offered from the rows of its callees. */
    private static List<String> seededInputs(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Db db = compilation.db();
        var surface = db.ask(new Shapes.CheckSurface("repro.lift")).value();
        var behavior = Adequacy.specOf(surface, "f");
        InputReading input = Adequacy.inputReadingOf(db, "repro.lift", behavior);
        AnalysisBody analysis = db.ask(new Bodies.Observable("repro.lift")).value()
                .analysisBodies().get("f");
        MeasuredInput subject = Adequacy.subjectOf(db, "repro.lift", behavior, input);
        Generator.CandidateCheck check = (_, _) -> new Generator.CandidateCheck.Built.NothingBuiltIt();
        return CallExampleSeeds.rowsFor(db, "repro.lift", subject, input, analysis, check,
                        List.of(), true, 50).stream()
                .map(row -> row.inputs().stream().map(FixtureTemplate::text).toList().toString())
                .toList();
    }
}
