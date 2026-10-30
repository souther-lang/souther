package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.check.AnalysisBody;
import souther.compiler.inputs.InputReading;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.partition.MeasuredInput;

import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

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

    private static final String THE_WHOLE_AND_ITS_FIELD = """
            module repro.lift
            data S = { score: Int }
            behavior inspect : (item: S, score: Int) -> Bool
            let inspect (item, score) = item.score == score
            example inspect
                | (S { score = 50 }, 50) -> true
                | (S { score = 7 }, 49) -> false
            behavior f : (s: S) -> Bool
            let f (s) = inspect(s, s.score)
            """;

    private static final String THE_FIELD_AND_ITS_WHOLE = """
            module repro.lift
            data S = { score: Int }
            behavior inspect : (score: Int, item: S) -> Bool
            let inspect (score, item) = item.score == score
            example inspect
                | (50, S { score = 50 }) -> true
                | (49, S { score = 7 }) -> false
            behavior f : (s: S) -> Bool
            let f (s) = inspect(s.score, s)
            """;

    private static final String THE_LIST_AND_THE_FIELD_OF_AN_ELEMENT = """
            module repro.lift
            data S = { score: Int }
            behavior inspect : (items: List<S>, score: Int) -> Bool
            let inspect (items, score) = List.length(items) == score
            example inspect
                | ([S { score = 1 }], 1) -> true
                | ([S { score = 1 }], 2) -> false
            behavior f : (ss: List<S>) -> Bool
            let f (ss) = List.fold((acc, s) -> acc && inspect(ss, s.score), true, ss)
            """;

    private static final String TWO_FIELDS_OF_ONE_ELEMENT = """
            module repro.lift
            data P = { a: Int, b: Int }
            behavior inspect : (items: List<P>, a: Int, b: Int) -> Bool
            let inspect (items, a, b) = a == b
            example inspect
                | ([P { a = 1, b = 2 }, P { a = 3, b = 4 }], 1, 4) -> false
                | ([P { a = 1, b = 2 }, P { a = 5, b = 6 }], 1, 2) -> false
            behavior f : (ps: List<P>) -> Bool
            let f (ps) = List.fold((acc, p) -> acc && inspect(ps, p.a, p.b), true, ps)
            """;

    private static final String A_SUM_AND_A_FIELD_OF_ITS_CASE = """
            module repro.lift
            data Playing = { score: Int }
            data State = Playing | Out
            behavior inspect : (item: State, score: Int) -> Bool
            let inspect (item, score) =
                match item with
                    | Out -> false
                    | Playing as q -> q.score == score
            example inspect
                | (Playing { score = 50 }, 50) -> true
                | (Playing { score = 7 }, 49) -> false
            behavior f : (s: State) -> Bool
            let f (s) =
                match s with
                    | Out -> false
                    | Playing as p -> inspect(s, p.score)
            """;

    private static final String A_FIELD_OF_A_NEWTYPE = """
            module repro.lift
            data Score = Int
            data S = { score: Score }
            behavior inspect : (item: S, score: Score) -> Bool
            let inspect (item, score) = item.score == score
            example inspect
                | (S { score = Score(50) }, Score(50)) -> true
                | (S { score = Score(7) }, Score(49)) -> false
            behavior f : (s: S) -> Bool
            let f (s) = inspect(s, s.score)
            """;

    private static final String A_MAP_AND_AN_ENTRY_OF_IT = """
            module repro.lift
            behavior inspect : (all: Map<String, Int>, key: String, n: Int) -> Bool
            let inspect (all, key, n) = Map.size(all) == n
            example inspect
                | ([("a", 1), ("b", 2)], "a", 1) -> false
                | ([("c", 1), ("d", 2)], "c", 2) -> false
            behavior f : (m: Map<String, Int>) -> Bool
            let f (m) = Map.size(Map.filterEntries((k, v) -> inspect(m, k, v), m)) == 0
            """;

    @Test
    void twoFieldsOfOneElementAreHandedTheListOnlyWhenOneElementHoldsBoth() {
        assertEquals(List.of("[[P { a = 1, b = 2 }, P { a = 5, b = 6 }]]"),
                seededInputs(TWO_FIELDS_OF_ONE_ELEMENT),
                "the row whose two values are in two elements is no call of the caller's");
    }

    @Test
    void aSumAndAFieldOfOneOfItsCasesAreHandedTheCaseTheRowHolds() {
        assertEquals(List.of("[Playing { score = 50 }]"),
                seededInputs(A_SUM_AND_A_FIELD_OF_ITS_CASE));
    }

    @Test
    void aFieldOfANewtypeIsReadAsTheDeclarationsWearIt() {
        List<String> rows = seededInputs(A_FIELD_OF_A_NEWTYPE);
        assertEquals(1, rows.size(), () -> "only the row that agrees with itself: " + rows);
        assertTrue(rows.getFirst().contains("50"), rows::toString);
    }

    @Test
    void aMapAndAnEntryOfItAreHandedTheMapOnlyWhenOneEntryHoldsBoth() {
        List<String> rows = seededInputs(A_MAP_AND_AN_ENTRY_OF_IT);
        assertEquals(1, rows.size(), () -> "the key and the value are of one entry: " + rows);
        assertTrue(rows.getFirst().contains("(\"a\", 1)"), rows::toString);
    }

    @Test
    void aListAndTheFieldOfOneOfItsElementsAreTheListWhenSomeElementHoldsTheValue() {
        assertEquals(List.of("[[S { score = 1 }]]"),
                seededInputs(THE_LIST_AND_THE_FIELD_OF_AN_ELEMENT),
                "the row whose value no element holds lifts to nothing");
    }

    @Test
    void aWholeInputAndOneOfItsFieldsAreOneRecordWhenTheRowAgreesWithItself() {
        assertEquals(List.of("[S { score = 50 }]"), seededInputs(THE_WHOLE_AND_ITS_FIELD),
                "the row whose field is not the whole's field lifts to nothing");
    }

    @Test
    void theOrderTheWholeAndItsFieldAreHandedInDecidesNothing() {
        assertEquals(List.of("[S { score = 50 }]"), seededInputs(THE_FIELD_AND_ITS_WHOLE));
    }

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

    @Test
    void theDecoderIsAskedAboutNoMoreRowsThanTheLimitHoweverManyTheCalleeWrites() {
        int fewRows = decoderAskedFor(rowsOfACallee(10), 3);
        int manyRows = decoderAskedFor(rowsOfACallee(40), 3);
        assertEquals(fewRows, manyRows,
                "what the decoder is asked depends on the limit and not on the rows written");
    }

    private static String rowsOfACallee(int rows) {
        StringBuilder out = new StringBuilder("""
                module repro.lift
                data S = { score: Int }
                behavior f : (s: S) -> Bool
                let f (s) = isFifty(s.score)
                behavior isFifty : (n: Int) -> Bool
                let isFifty (n) = n == 50
                example isFifty
                """);
        for (int i = 0; i < rows; i++) {
            out.append("    | (").append(100 + i).append(") -> false\n");
        }
        // The caller has written every row the lift would offer, which is the rows it skips
        // without asking the decoder when nothing is built around a position.
        out.append("example f\n");
        for (int i = 0; i < rows; i++) {
            out.append("    | (S { score = ").append(100 + i).append(" }) -> false\n");
        }
        return out.toString();
    }

    /** How many times the decoder is asked to build a value while {@code f} is seeded. */
    private static int decoderAskedFor(String source, int limit) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Db db = compilation.db();
        var behavior = Adequacy.specOf(db.ask(new Shapes.CheckSurface("repro.lift")).value(), "f");
        InputReading input = Adequacy.inputReadingOf(db, "repro.lift", behavior);
        AnalysisBody analysis = db.ask(new Bodies.Observable("repro.lift")).value()
                .analysisBodies().get("f");
        MeasuredInput subject = Adequacy.subjectOf(db, "repro.lift", behavior, input);
        AtomicInteger asked = new AtomicInteger();
        Generator.CandidateCheck check = (_, _) -> {
            asked.incrementAndGet();
            return new Generator.CandidateCheck.Built.NothingBuiltIt();
        };
        CallExampleSeeds.rowsFor(db, "repro.lift", subject, input, analysis, check, List.of(),
                true, limit);
        return asked.get();
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
