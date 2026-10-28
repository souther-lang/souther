package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A field read off a construction is worked out beside the construction's other parts, and the
 * construction is made all the same. What the comparison tells of its operations is every one only
 * where none of that can stop a run: a construction of a type with an invariant is checked when it
 * is made, and a part that is a name stands for what was worked out where it was bound.
 */
class AFieldReadOffAConstructionIsToldOnlyWhereTheConstructionEndsNoRunTest {

    private static UndividedByARelation.Working told(String data, String constructs,
                                                     String body) {
        String source = """
                module g

                data Yes
                data No
                %s

                behavior classify : (n: Int, k: Int) -> Yes | No
                    %s
                let classify (n, k) = %s

                example classify
                    | "one" : (1, 1) -> Yes
                """.formatted(data, constructs, body);
        ReadComparisons read = ReadComparisons.of(source, "classify");
        ComparisonReadings.Reading against = read.only();
        AffineReading.OfAComparison reading = AffineReading.read(
                ((ComparisonReadings.Stated.AComparison) against.statement()).comparison(),
                against.reads(), read.inputs().reading(read.rules()));
        return AffineReading.OfAComparison.workingOf(reading);
    }

    private static final String RECORD = "data P = { x: Int, y: Int }";

    @Test
    void aConstructionOfLiteralsThatEndsNoRunIsToldEveryOperation() {
        UndividedByARelation.Working working = told(RECORD, "",
                "{\n    let p = P { x = n, y = 1 }\n    if p.x >= k then Yes else No\n}");
        assertNotNull(working);
        assertTrue(working.exact(), working.toString());
    }

    @Test
    void aConstructionOfATypeWithAnInvariantIsNotToldEveryOperation() {
        UndividedByARelation.Working working = told(
                RECORD + "\ndata Q = { x: Int, y: Int }\n    invariant y >= 0", "constructs Q",
                "{\n    let p = Q { x = n, y = 1 }\n    if p.x >= k then Yes else No\n}");
        assertFalse(working.exact(), working.toString());
    }

    @Test
    void aPartThatNamesWhatWasWorkedOutElsewhereIsNotToldEveryOperation() {
        UndividedByARelation.Working working = told(RECORD, "",
                "{\n    let o = n + 1\n    let p = P { x = n, y = o }\n"
                        + "    if p.x >= k then Yes else No\n}");
        assertFalse(working.exact(), working.toString());
    }
}
