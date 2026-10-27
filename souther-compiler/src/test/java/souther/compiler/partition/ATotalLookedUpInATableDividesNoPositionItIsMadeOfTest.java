package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A total one comparison holds against every row of a table is cut at each row's threshold, and the
 * positions it is made of are divided by none of them: a value of one position that settles the
 * comparison at one threshold leaves the next either way, so the outcome is not the same through
 * the class.
 */
class ATotalLookedUpInATableDividesNoPositionItIsMadeOfTest {

    private static final String DECLARATIONS = """
            data N = { v: Int }
                invariant v >= 0
            data Row = { grade: Int, lowerBound: Int }
            """;

    private static final String GRADE_OF = """
            let gradeOf (m: Int): Int =
                List.fold((acc, r) -> if r.lowerBound <= m then r.grade else acc, 1, table)
            """;

    private static final String TWO_ROWS = """
            let table: List<Row> = [ Row { grade = 2, lowerBound = 100 },
                                     Row { grade = 3, lowerBound = 200 } ]
            """;

    private static final String ONE_ROW = """
            let table: List<Row> = [ Row { grade = 2, lowerBound = 100 } ]
            """;

    @Test
    void aTotalCutAtEveryRowOfATableDividesNeitherPosition() {
        assertEquals(List.of(), classesAt(TWO_ROWS, "gradeOf(a.v + b.v)", "a.v"));
        assertEquals(List.of(), classesAt(TWO_ROWS, "gradeOf(a.v + b.v)", "b.v"));
    }

    /** The control: a total cut at one place divides its positions where one settles it. */
    @Test
    void aTotalCutAtOnePlaceStillDividesThePositionsAtTheValueThatSettlesIt() {
        assertFalse(classesAt(ONE_ROW, "gradeOf(a.v + b.v)", "a.v").isEmpty());
    }

    /** The control: two comparisons are two computations, and neither is the other's table. */
    @Test
    void twoComparisonsOfOneTotalAreNotATable() {
        String body = "if a.v + b.v >= 200 then 3 else if a.v + b.v >= 100 then 2 else 1";
        assertFalse(classesAt(TWO_ROWS, body, "a.v").isEmpty());
    }

    private static List<String> classesAt(String table, String body, String path) {
        Compilation compilation = Compilation.ofSource("module demo\n\n" + DECLARATIONS + table
                + GRADE_OF + """

                behavior f : (a: N, b: N) -> Int

                let f (a, b) =
                    %s
                """.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        PartitionEvidence evidence =
                compilation.db().ask(new Adequacy.Coverage("demo")).value().get("f");
        return evidence.axes().stream().filter(axis -> axis.path().equals(path))
                .flatMap(axis -> axis.classes().stream()).toList();
    }
}
