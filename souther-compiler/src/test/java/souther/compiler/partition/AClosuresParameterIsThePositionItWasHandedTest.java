package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison written inside a closure a combinator was handed is a comparison about the position
 * the combinator handed it.
 *
 * <p>The same predicate twice, once on a bare position and once on the elements of a list. They are
 * one rule about one kind of value, and the report said one of them divided a position and the
 * other divided nothing — not because the element had no rule but because nothing could say which
 * position the closure's parameter stood for.
 *
 * <p>Which the library's own signature says. What is missing from the tree the derivation reads is
 * the operation: a fold that only grows a collection is rewritten into a walk over a builder before
 * the tree is emitted, so by then nothing in it says an element came from anywhere. So the relation
 * is read where the operation still stands and carried by binding, and the walk that resolves a
 * position gains a third way for a name to reach one — beside a parameter, and beside what a
 * {@code let} holds.
 */
class AClosuresParameterIsThePositionItWasHandedTest {

    private static final String MODULE = "example.people";

    private static final String MODEL = """
            module example.people

            data Age = Int
                invariant value >= 0
            data Person =
                { age: Age
                }
            data Verdict = Included | Excluded

            behavior classify : (age: Age) -> Verdict
            let classify (age) = {
                guard age.value >= 18 else Excluded
                Included
            }

            behavior select : (people: List<Person>) -> List<Person>
            let select (people) =
                List.filter(p -> p.age.value >= 18, people)
            """;

    private static Map<String, PartitionEvidence> measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage(MODULE)).value();
        assertNotNull(coverage, "the model under test compiles");
        return coverage;
    }

    private static PartitionEvidence.AxisCoverage only(PartitionEvidence evidence) {
        assertEquals(1, evidence.axes().size(),
                () -> "one axis: " + evidence.axes().stream()
                        .map(PartitionEvidence.AxisCoverage::path).toList());
        return evidence.axes().get(0);
    }

    /** The element of the list is where the line falls, spelled as the coordinate it is. */
    @Test
    void theLineIsDrawnAtTheElement() {
        assertEquals("people[*].age", only(measured().get("select")).path());
    }

    /**
     * And it divides into what the same rule divides a bare position into.
     *
     * <p>The classes are compared and not merely counted. One rule on one kind of value gives one
     * division, and a report where the two came out differently would be about where the value sits
     * rather than about what the model says of it.
     */
    @Test
    void itDividesIntoWhatTheSameRuleDividesABarePositionInto() {
        String bare = only(measured().get("classify")).classes().toString();
        String inside = only(measured().get("select")).classes().toString();

        assertEquals(bare.replace("age/", "×/"), inside.replace("people[*].age/", "×/"),
                () -> "the same rule divides the same values: " + bare + " and " + inside);
    }

    /** And nothing is left saying the position could not be read. */
    @Test
    void nothingIsLeftSayingTheElementCouldNotBeRead() {
        PartitionEvidence select = measured().get("select");

        assertEquals(List.of(), select.notRead().stream()
                        .filter(each -> each.at().equals("people[*].age")).toList(),
                () -> "nothing about the element went unread: " + select.notRead());
        assertTrue(select.notDerivable().stream()
                        .noneMatch(each -> each.at().toString().equals("people[*].age")),
                () -> "and the element is measured: " + select.notDerivable());
    }

    /**
     * What a combinator is handed out of another operation's answer is not one of these, and the
     * rule written about it is still named.
     *
     * <p>The container is what a {@code map} answered, so an element of it is not a position of this
     * behavior's input — it is a value made from one, and what a rule about it means for the input
     * is a question nothing here answers. No line is drawn: reported as a position, it would be
     * drawn where no row can reach it and the report would name a coordinate the model does not
     * have.
     *
     * <p>But the rule is not silent. An author who filters what a {@code map} answered wrote a
     * comparison, and a reading that placed it nowhere said nothing at all — which reads as a model
     * that states no rule there. What is said instead is where the values came from, and that what
     * the rule says about them here is not worked out.
     */
    @Test
    void anElementOfWhatAnotherOperationAnsweredNamesNoPosition() {
        String derived = MODEL + """

            data Score = Int

            behavior scored : (people: List<Person>) -> List<Score>
            let scored (people) =
                List.filter(s -> s.value >= 18,
                    List.map(q -> Score(q.age.value + 100), people))
            """;
        Compilation compilation = Compilation.ofSource(derived, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        PartitionEvidence scored =
                compilation.db().ask(new Adequacy.Coverage(MODULE)).value().get("scored");
        assertNotNull(scored, "the model under test compiles");

        assertEquals(List.of(), scored.axes().stream()
                        .map(PartitionEvidence.AxisCoverage::path).toList(),
                "no line is drawn on a position this behavior's input does not have");
        assertEquals(List.of("people[*]"), scored.notRead().stream()
                        .filter(each -> each.reason()
                                == UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE)
                        .map(PartitionEvidence.NotRead::at).toList(),
                () -> "and the rule is named, at the position its values came from: "
                        + scored.notRead());
    }
}
