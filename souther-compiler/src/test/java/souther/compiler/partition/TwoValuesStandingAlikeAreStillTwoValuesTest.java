package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Two values of the module sitting in the same classes are two things to write a row against.
 *
 * <p>Where a row's values sit is what orders this search: how far a row moves from the value it is
 * written against is what the walk minimises, and that is counted in classes. What the values
 * <em>are</em> is a different question, and it is the one the model answers — a rule relating two
 * fields accepts one pair and refuses another, and both pairs can sit in the same classes.
 *
 * <p>So the two are one candidate for the ordering and two candidates for the search. Taken as one,
 * a class the model can hold a row for came back with nothing: the first of them was refused, and
 * the second — which builds, at the same distance, in the same classes — was never tried.
 */
class TwoValuesStandingAlikeAreStillTwoValuesTest {

    /**
     * Two values in the same classes, and only one of them can hold the class {@code hi} is owed.
     *
     * <p>Both sit at {@code lo} in its lower class and at {@code hi} in its upper one. A row for the
     * lower class of {@code hi} writes {@code hi} at the bottom of that class, which the rule
     * refuses beside {@code tight}'s {@code lo} and allows beside {@code loose}'s. Moving
     * {@code lo} as well does not save {@code tight}: its other class is above the one it is in,
     * and further from what the row needs.
     */
    private static final String ALIKE = """
            module example.trip

            data Amount = Int
                invariant value >= 0

            data Request = { lo: Amount, hi: Amount }
                invariant lo.value <= hi.value

            data Accepted = { at: String }

            let tight = Request { lo = Amount(50), hi = Amount(70) }
            let loose = Request { lo = Amount(0), hi = Amount(70) }

            behavior submit : (request: Request) -> Accepted
                constructs Accepted

            let submit (request) = {
                guard request.lo.value <= 50 else Accepted { at = "wide" }
                guard request.hi.value <= 60 else Accepted { at = "tall" }
                Accepted { at = "now" }
            }
            """;

    /**
     * The second of them answers the class the first cannot be written for.
     *
     * <p>Read by where the values sit, the two are one origin and the search ends at the first. What
     * is asserted here is the row, and the row names the value that builds.
     */
    @Test
    void theValueThatBuildsIsTriedThoughAnotherStandsWhereItDoes() {
        assertEquals("Request { ...loose, hi = Amount(0) }", rowFor("request.hi/0 <= x <= 60"));
    }

    /** And the value written first is still the one used where both can be. */
    @Test
    void theFirstOfThemIsStillTheOneUsedWhereBothCanBe() {
        assertEquals("Request { ...tight, lo = Amount(51) }", rowFor("request.lo/50 < x"));
    }

    private static String rowFor(String classId) {
        Compilation compilation = Compilation.ofSource(ALIKE, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all =
                Adequacy.generatedOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(all, "the model under test compiles");
        Adequacy.Filling filling = all.get("submit");
        assertNotNull(filling, "the behavior under test is generated for");
        for (Generator.GeneratedRow row : filling.composed().rows()) {
            for (Generator.Purpose purpose : row.purposes()) {
                if (purpose instanceof Generator.Purpose.ForAClass about
                        && about.classId().equals(classId)) {
                    return String.join(", ",
                            row.inputs().stream().map(FixtureTemplate::text).toList());
                }
            }
        }
        throw new AssertionError("no row was offered for " + classId + ": "
                + filling.composed().discharge().classes().values());
    }
}
