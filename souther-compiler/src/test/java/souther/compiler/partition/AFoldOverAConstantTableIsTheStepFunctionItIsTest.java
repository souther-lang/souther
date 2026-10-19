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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fold over a constant table that keeps the last row whose bound is met answers the step function
 * the table draws, so a comparison over what it answers is read at the bounds the table draws.
 *
 * <p>The step is one {@code if} in the source, applied once per row, so what is asserted is that
 * each application is read as its own. The same table written out as a chain of {@code if}s is the
 * reading to compare with: the classes of the input are the ones that chain draws.
 */
class AFoldOverAConstantTableIsTheStepFunctionItIsTest {

    private static final String ASCENDING = """
            [ Row { grade = 1, lowerBound = 100 }, Row { grade = 2, lowerBound = 200 },
              Row { grade = 3, lowerBound = 300 } ]""";

    private static final String BY_HAND = """
            if pay >= 300 then 3 else if pay >= 200 then 2 else if pay >= 100 then 1 else 0""";

    @Test
    void whateverIsDoneWithTheGradeIsReadAtEveryBoundOfTheTable() {
        for (String condition : List.of("computed < 2", "computed - cur < 2",
                "Int.abs(computed - cur) < 2")) {
            PartitionEvidence folded = measured(ASCENDING, "r.lowerBound <= monthly", condition);
            assertEquals(List.of(), notRead(folded), condition);
            assertEquals(classesOf(measuredByHand(BY_HAND, condition), "pay"),
                    classesOf(folded, "pay"), condition);
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

    /** A walk over no row ends with its seed, and over one row it draws that row's bound. */
    @Test
    void aTableOfNoRowIsItsSeedAndOfOneRowIsOneBound() {
        PartitionEvidence none = measured("[]", "r.lowerBound <= monthly", "computed < 2");
        assertEquals(List.of(), notRead(none));
        PartitionEvidence one = measured("[ Row { grade = 1, lowerBound = 100 } ]",
                "r.lowerBound <= monthly", "computed < 1");
        assertEquals(List.of(), notRead(one));
        assertEquals(List.of("pay/x < 100", "pay/100 <= x"), classesOf(one, "pay"));
    }

    /** What the step selects may be a number as well as a row. */
    @Test
    void aWalkThatSelectsANumberIsReadAsOneThatSelectsARow() {
        PartitionEvidence measured = measure(Compilation.ofSource("""
                module demo

                data Row = { grade: Int, lowerBound: Int }
                data Ok
                data No
                let table: List<Row> = %s
                behavior f : (pay: Int) -> Ok | No
                let f (pay) = {
                    let computed = List.fold((acc, r) -> if r.lowerBound <= pay then r.grade else acc,
                        0, table)
                    guard computed < 2 else No
                    Ok
                }
                """.formatted(ASCENDING), "Main"), "f");
        assertEquals(List.of(), notRead(measured));
        assertEquals(List.of("pay/x < 100", "pay/100 <= x < 200", "pay/200 <= x < 300",
                "pay/300 <= x"), classesOf(measured, "pay"));
    }

    /** A step that can end a run for any reason is not one whose earlier applications are dropped. */
    @Test
    void aStepThatMayEndARunIsNotReadAsAChoice() {
        for (String selects : List.of("r.lowerBound / monthly <= 1",
                "r.lowerBound + monthly >= 0", "r.lowerBound * monthly >= 0")) {
            assertFalse(notRead(measured(ASCENDING, selects, "computed < 2")).isEmpty(), selects);
        }
    }

    /** A seed no form says keeps the reason it has. */
    @Test
    void aSeedNoFormSaysKeepsItsReason() {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Row = { grade: Int, lowerBound: Int }
                data Ok
                data No
                let table: List<Row> = %s
                behavior f : (cur: Int, pay: Int) -> Ok | No
                let f (cur, pay) = {
                    let computed = List.fold((acc, r) -> if r.lowerBound <= pay then r.grade else acc,
                        cur * pay, table)
                    guard computed < 2 else No
                    Ok
                }
                """.formatted(ASCENDING), "Main");
        assertTrue(notRead(measure(compilation, "f")).toString().contains("NON_AFFINE_PRODUCT"));
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
        assertFalse(notRead(measure(compilation, "f")).isEmpty());
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
                """.formatted(table, selects, condition), "Main"), "f");
    }

    private static PartitionEvidence measuredByHand(String grade, String condition) {
        return measure(Compilation.ofSource("""
                module demo

                data Ok
                data No
                behavior f : (cur: Int, pay: Int) -> Ok | No
                let f (cur, pay) = {
                    let computed = %s
                    guard %s else No
                    Ok
                }
                """.formatted(grade, condition), "Main"), "f");
    }

    private static PartitionEvidence measure(Compilation compilation, String behavior) {
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation.db().ask(new Adequacy.Coverage("demo")).value().get(behavior);
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
