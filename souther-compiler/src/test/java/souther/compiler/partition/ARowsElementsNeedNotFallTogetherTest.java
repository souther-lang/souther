package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.WhatTheRowsReached;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a row covers at a position inside a sequence is every class its elements fell in.
 *
 * <p>One row and several classes, which is a shape no other position has. A list holding one element
 * under a line and one over it stands on both sides of it, and there is no element among them a
 * reading is entitled to pick — read as one value, the row would cover whichever element the walk
 * met first and the class beside it would be reported as owed a row the author has already written.
 *
 * <p>And a list holding no element is a row that was read and covers nothing there, which is not the
 * same as a row nothing could be read from. Told apart because they mean opposite things: one is a
 * gap and the other is a measurement that could not look.
 */
class ARowsElementsNeedNotFallTogetherTest {

    private static final String MODULE = "example.roster";

    private static final String MODEL = """
            module example.roster

            data Person = { age: Int }
            data Count = Int

            behavior adults : (people: List<Person>) -> Count
                constructs Count
            let adults (people) =
                Count(List.length(List.filter(p -> p.age >= 18, people)))

            example adults
                | "ROW" : (PEOPLE) -> Count(N)
            """;

    private static PartitionEvidence.AxisCoverage elementAxis(String people, String count) {
        Compilation compilation = Compilation.ofSource(
                MODEL.replace("PEOPLE", people).replace("N", count), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage(MODULE)).value();
        assertNotNull(coverage, () -> "the model under test compiles: " + people);
        PartitionEvidence adults = coverage.get("adults");
        assertNotNull(adults, "adults was measured");
        assertEquals(1, adults.axes().size(),
                () -> "one axis: " + adults.axes().stream()
                        .map(PartitionEvidence.AxisCoverage::path).toList());
        return adults.axes().get(0);
    }

    /** The two classes the guard leaves, whichever a row lands in. */
    @Test
    void theElementIsWhereTheLineFalls() {
        PartitionEvidence.AxisCoverage axis =
                elementAxis("[ Person { age = 20 } ]", "1");

        assertEquals("people[*].age", axis.path());
        assertEquals(List.of("people[*].age/x < 18", "people[*].age/18 <= x"), axis.classes());
    }

    /** One element, one class. */
    @Test
    void aListOfOneCoversTheClassItsElementIsIn() {
        assertEquals(Set.of("people[*].age/18 <= x"),
                WhatTheRowsReached.at(elementAxis("[ Person { age = 20 } ]", "1")).covered());
    }

    /**
     * Two elements either side of the line, and the row covers both classes.
     *
     * <p>The whole of what this is about. Both are values the row wrote at the position, so both
     * classes have a row in them, and neither is owed one.
     */
    @Test
    void aListWithElementsEitherSideOfTheLineCoversBoth() {
        PartitionEvidence.AxisCoverage axis =
                elementAxis("[ Person { age = 20 }, Person { age = 10 } ]", "1");

        assertEquals(Set.of("people[*].age/18 <= x", "people[*].age/x < 18"),
                WhatTheRowsReached.at(axis).covered());
        assertEquals(0, WhatTheRowsReached.at(axis).unclassifiedRows(),
                "and the row said where it was, at every element it wrote");
    }

    /**
     * An empty list is read and covers nothing, which is not a row that could not be read.
     *
     * <p>The count of rows that could not say is what tells the two apart: a measurement that could
     * not look leaves a class undecided, and a row that looked and wrote no element leaves it
     * plainly uncovered.
     */
    @Test
    void anEmptyListIsReadAndCoversNothing() {
        PartitionEvidence.AxisCoverage axis = elementAxis("[ ]", "0");

        assertEquals(Set.of(), WhatTheRowsReached.at(axis).covered());
        assertEquals(0, WhatTheRowsReached.at(axis).unclassifiedRows(),
                "the row was read: it wrote no element, which is not a value nothing could read");
        assertTrue(axis.classes().size() > WhatTheRowsReached.at(axis).covered().size(),
                "so the classes it did not reach are owed a row");
    }
}
