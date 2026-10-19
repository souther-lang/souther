package souther.compiler.partition;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Measurement;
import souther.compiler.query.PartitionEvidence;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A fold over a constant table that keeps the last row whose bound is met answers the step function
 * the table draws, so a comparison over what it answers is read at the bounds the table draws.
 *
 * <p>The step is one {@code if} in the source, applied once per row, so what is asserted is that
 * each application is read as its own: the classes of the input are the ones the bounds draw, and
 * which row is the last one met follows the order the rows are written in.
 */
class AFoldOverAConstantTableIsTheStepFunctionItIsTest {

    private static final String ASCENDING = """
            [ Row { grade = 1, lowerBound = 100 }, Row { grade = 2, lowerBound = 200 },
              Row { grade = 3, lowerBound = 300 } ]""";

    @Test
    void whateverIsDoneWithTheGradeIsReadAtEveryBoundOfTheTable() {
        for (String condition : List.of("computed < 2", "computed - cur < 2",
                "Int.abs(computed - cur) < 2")) {
            PartitionEvidence measured = measured(ASCENDING, "r.lowerBound <= monthly", condition);
            assertEquals(List.of(), notRead(measured), condition);
            assertEquals(List.of("pay/x < 100", "pay/100 <= x < 200", "pay/200 <= x < 300",
                    "pay/300 <= x"), classesOf(measured, "pay"), condition);
        }
    }

    /** Bounds written out of order, and one written twice, are the bounds of the table all the same. */
    @Test
    void boundsWrittenOutOfOrderAreReadAtEachOfThem() {
        PartitionEvidence measured = measured("""
                [ Row { grade = 1, lowerBound = 200 }, Row { grade = 2, lowerBound = 100 },
                  Row { grade = 3, lowerBound = 200 } ]""", "r.lowerBound <= monthly",
                "computed < 3");
        assertEquals(List.of(), notRead(measured));
        assertEquals(List.of("pay/x < 100", "pay/100 <= x < 200", "pay/200 <= x"),
                classesOf(measured, "pay"));
    }

    /** A step that can divide may stop a run, so a later row is not what the walk ends with. */
    @Test
    void aStepThatCanStopARunIsNotReadAsAChoice() {
        assertFalse(notRead(measured(ASCENDING, "r.lowerBound / monthly <= 1", "computed < 2"))
                .isEmpty());
    }

    /** A table an input decides is no step function written down. */
    @Test
    void aTableTheInputDecidesIsNotAStepFunction() {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Row = { grade: Int, lowerBound: Int }
                data Ok
                data No
                behavior f : (pay: Int, rows: List<Row>) -> Ok | No
                let f (pay, rows) = {
                    let computed = List.fold((acc, r) -> if r.lowerBound <= pay then r else acc,
                        Row { grade = 0, lowerBound = 0 }, rows).grade
                    guard computed < 2 else No
                    Ok
                }
                """, "Main");
        assertFalse(notRead(measure(compilation)).isEmpty());
    }

    private static PartitionEvidence measured(String table, String selects, String condition) {
        return measure(Compilation.ofSource("""
                module demo

                data Row = { grade: Int, lowerBound: Int }
                data Ok
                data No
                let table: List<Row> = %s
                let rowFor (monthly: Int): Row =
                    List.fold((acc, r) -> if %s then r else acc,
                        Row { grade = 0, lowerBound = 0 }, table)
                behavior f : (cur: Int, pay: Int) -> Ok | No
                let f (cur, pay) = {
                    let computed = rowFor(pay).grade
                    guard %s else No
                    Ok
                }
                """.formatted(table, selects, condition), "Main"));
    }

    private static PartitionEvidence measure(Compilation compilation) {
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation.db().ask(new Adequacy.Coverage("demo")).value().get("f");
    }

    private static List<String> notRead(PartitionEvidence measured) {
        return measured.notRead().stream()
                .map(each -> each.at() + ": " + each.reason())
                .distinct()
                .sorted()
                .collect(Collectors.toList());
    }

    private static List<String> classesOf(PartitionEvidence measured, String path) {
        if (!(measured.partitioned()
                instanceof Measurement.Complete<List<PartitionEvidence.AxisCoverage>> complete)) {
            throw new AssertionError("the partition was measured: " + measured.partitioned());
        }
        return complete.value().stream()
                .filter(axis -> axis.path().equals(path))
                .flatMap(axis -> axis.classes().stream())
                .toList();
    }
}
