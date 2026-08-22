package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A pair two positions inside one sequence make is one element standing in both.
 *
 * <p>A row's values at {@code people[*].age} and at {@code people[*].status} are its elements' ages
 * and its elements' statuses, and which went with which is the whole of what a pair says. Read off
 * the two sets of classes, the pairs one row covers are every combination of them — so a list
 * holding one person under a line and one who is active is counted as evidence for a person both
 * over the line and active, which none of its elements is.
 *
 * <p>Which is the answer a coverage measure exists to refuse. A combination a row sits in is what
 * says the combination can be reached (ADR-0091); two existential witnesses taken separately and
 * put together are not one witness.
 *
 * <p>So each value carries the elements taken to reach it, keyed by the step they were taken at,
 * and two values stand together exactly where every step they took together was taken at the same
 * element. Every case follows from that one sentence: two positions under one person agree about
 * the person; two under different parameters agree about nothing and stand freely; and a position
 * inside no sequence takes no step and stands with everything.
 */
class APairIsOneElementInTwoClassesTest {

    private static final String MODULE = "example.people";

    private static final String MODEL = """
            module example.people

            data Status = Active | Inactive
            data Person =
                { age: Int
                , status: Status
                }

            behavior select : (people: List<Person>) -> List<Person>
            let select (people) =
                List.filter(p -> p.age >= 18 && p.status == Active, people)

            example select
                | "ROW" : (PEOPLE) -> [ ]
            """;

    private static Compilation compiled(String people) {
        Compilation compilation =
                Compilation.ofSource(MODEL.replace("PEOPLE", people), "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return compilation;
    }

    private static PartitionEvidence measured(String people) {
        PartitionEvidence select = compiled(people).db()
                .ask(new Adequacy.Coverage(MODULE)).value().get("select");
        assertNotNull(select, () -> "the model under test compiles: " + people);
        return select;
    }

    /** The counterexample: no element is both over the line and active. */
    @Test
    void twoElementsDoNotWitnessTheCombinationNeitherIsIn() {
        PartitionEvidence select = measured("""
                [ Person { age = 17, status = Active },
                  Person { age = 20, status = Inactive } ]""");

        assertEquals(4, select.pairs().total(), "two classes at each of two positions");
        assertEquals(2, select.pairs().covered(),
                () -> "the two its elements are in, and not the two neither is: "
                        + select.pairs());
    }

    /** And each position still covers both of its classes, since each of its values is its own. */
    @Test
    void eachPositionStillCoversBothOfItsClasses() {
        PartitionEvidence select = measured("""
                [ Person { age = 17, status = Active },
                  Person { age = 20, status = Inactive } ]""");

        assertEquals(List.of(Set.of("people[*].age/x < 18", "people[*].age/18 <= x"),
                        Set.of("Active", "Inactive")),
                select.axes().stream().map(PartitionEvidence.AxisCoverage::covered).toList());
    }

    /**
     * And the search offers a row for the combinations that row is not evidence for.
     *
     * <p>The same counterexample, put to the other reader. What a row covers is one question, and a
     * search answering it its own way went on treating every combination as filled while the report
     * was still calling two of them untried -- so both are asked of one rule here.
     */
    @Test
    void theSearchOffersARowForTheCombinationsNeitherElementIsIn() {
        Map<String, Adequacy.Filling> generated = compiled("""
                [ Person { age = 17, status = Active },
                  Person { age = 20, status = Inactive } ]""").db()
                .ask(new Adequacy.Generated(MODULE)).value();
        assertNotNull(generated, "rows are offered");

        assertEquals(List.of("[Person { age = 17, status = Inactive }]",
                        "[Person { age = 18, status = Active }]"),
                generated.get("select").pairs().rows().stream()
                        .map(row -> row.inputs().get(0).text()).toList(),
                () -> "one row for each combination no element of the written row is in: "
                        + generated.get("select").pairs().reasons());
    }

    /** One element in both classes is a witness, and is counted as one. */
    @Test
    void oneElementInBothIsTheWitness() {
        PartitionEvidence select =
                measured("[ Person { age = 20, status = Active } ]");

        assertEquals(1, select.pairs().covered(),
                () -> "the one its element is in: " + select.pairs());
    }
}
