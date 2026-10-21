package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two paths are one where their head and their steps are, however each was made.
 *
 * <p>The steps of a path keep their own hash. What that must not change is what a path is equal to
 * and what it hashes as: a path made from a plain list and a path made by walking one field further
 * are the same path, and its steps are the list they were made from.
 */
class APathIsTheSameWhereItsStepsAreTest {

    private static final List<TermPath.Step> STEPS = List.of(
            new TermPath.Step.Field("cost"), new TermPath.Step.Element(),
            new TermPath.Step.Field("value"));

    @Test
    void pathsMadeApartFromTheSameStepsAreEqualAndHashAlike() {
        TermPath one = new TermPath("request", STEPS);
        TermPath other = new TermPath("request", new ArrayList<>(STEPS));

        assertEquals(one, other);
        assertEquals(one.hashCode(), other.hashCode());
        assertEquals(Set.of(one), new HashSet<>(List.of(other)));
    }

    @Test
    void aPathMadeByWalkingFurtherIsThePathMadeAtOnce() {
        TermPath walked = TermPath.of("request").then("cost");

        assertEquals(new TermPath("request", List.of(new TermPath.Step.Field("cost"))), walked);
        assertEquals(walked.hashCode(),
                new TermPath("request", List.of(new TermPath.Step.Field("cost"))).hashCode());
    }

    @Test
    void pathsThatDifferInAStepOrTheHeadAreNotEqual() {
        TermPath path = new TermPath("request", STEPS);

        assertNotEquals(path, new TermPath("request", STEPS.subList(0, 2)));
        assertNotEquals(path, new TermPath("other", STEPS));
        assertNotEquals(path, new TermPath("request", List.of(
                new TermPath.Step.Field("cost"), new TermPath.Step.Key(),
                new TermPath.Step.Field("value"))));
    }

    @Test
    void theStepsAreTheListTheyWereMadeFromAndCannotBeChanged() {
        TermPath path = new TermPath("request", STEPS);

        assertEquals(STEPS, path.steps());
        assertEquals(path.steps(), STEPS);
        assertEquals(STEPS.hashCode(), path.steps().hashCode());
        assertTrue(path.steps() instanceof java.util.RandomAccess);
        assertThrows(UnsupportedOperationException.class,
                () -> path.steps().add(new TermPath.Step.Element()));
    }
}
