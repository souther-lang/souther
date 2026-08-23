package souther.compiler;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How many a build has and how many its source has are one value where the operation says so.
 *
 * <p>{@code List.reverse} and {@code List.map} answer exactly as many as they were given, which
 * {@code souther.compiler.semantics.Cardinality.SAME} states — and it is stated as a relation between the two
 * values, not as a fact about either. So the size of the build and the size of the source are one
 * subject rather than two that have to be kept saying the same thing, and a guard written about
 * either is a guard about both.
 *
 * <p>Held here because that identification is about to become the answer everywhere. It is read from
 * the table that already declares the relation, and reading it there is right exactly while the
 * declaration is a semantic equality: {@code AT_MOST} is the same table's word for an operation that
 * may answer fewer, and the second half of this holds that such an operation is <em>not</em>
 * identified — a subject built from what an analysis merely happens to follow would tie what this
 * check can name to what it can currently prove.
 */
class ACardinalityPreservingBuildAndItsSourceAreOneSizeTest {

    private static final String DECLARES = """
            module m exposing ( Sized, use )

            data Sized = Int
                invariant value > 0

            behavior use : (xs: List<Int>) -> Sized
                constructs Sized
            """;

    private static List<Diagnostic> unproven(String source) {
        return Compiler.compileWithWarnings(source).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING)
                .filter(d -> d.code().equals("E2011")).toList();
    }

    /**
     * A guard on the source settles a clause about the build.
     *
     * <p>Which is only true if the two sizes are one subject. Were they two, the guard would have
     * spoken about one of them and the construction would be read against the other, and nothing
     * would carry across.
     */
    @Test
    void aGuardOnTheSourceSettlesAConstructionOverACardinalityPreservingBuild() {
        assertEquals(List.of(), unproven(DECLARES + """
                let use (xs) = {
                    guard List.length(xs) > 0
                        else Sized(1)
                    Sized(List.length(List.reverse(xs)))
                }
                """), "`reverse` answers exactly as many, so both sizes are the one value");

        assertEquals(List.of(), unproven(DECLARES + """
                let use (xs) = {
                    guard List.length(xs) > 0
                        else Sized(1)
                    Sized(List.length(List.map(x -> x + 1, xs)))
                }
                """), "and so does `map`, whatever it does to the elements");
    }

    /**
     * And an operation that may answer fewer is not identified with its source.
     *
     * <p>The control the first half needs: silence there would look the same if nothing were being
     * read at all. {@code filter} is declared {@code AT_MOST} by the same table, and a guard saying
     * the source is non-empty says nothing about how many survive it — so this construction stays the
     * unproven one it is.
     */
    @Test
    void aBuildThatMayAnswerFewerIsNotTheSameSizeAsItsSource() {
        assertEquals(1, unproven(DECLARES + """
                let use (xs) = {
                    guard List.length(xs) > 0
                        else Sized(1)
                    Sized(List.length(List.filter(x -> x > 0, xs)))
                }
                """).size(), "`filter` may answer fewer, so the source's size settles nothing");
    }
}
