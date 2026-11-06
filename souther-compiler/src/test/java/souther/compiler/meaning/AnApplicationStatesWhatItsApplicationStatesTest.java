package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.types.ACallOfAnOperation;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Saying which application of a closure a step was read on changes nothing of what it states: a
 * derivation concludes the same with every step of it said to be an application and without, and
 * a reader walking the premises reaches the same steps one further down.
 */
class AnApplicationStatesWhatItsApplicationStatesTest {

    private static final ACallOfAnOperation FOLD = new ACallOfAnOperation(
            ValueName.Stdlib.operation("List", "fold"),
            new ConstructOccurrence(SourceConstructOrigin.written(new WrittenOwner.Body("m", "g"),
                    0, SourceConstruct.CALL), OccurrenceLineage.ORIGINAL));

    /** Steps of every shape that conclude something of their own or hold others. */
    private static List<Derivation> steps() {
        Derivation held = new Derivation.Folded(true);
        Derivation failed = new Derivation.Folded(false);
        return List.of(held, failed, new Derivation.IfThenElse(held, failed, held),
                new Derivation.IfThenElse(failed, new Derivation.IfThenElse(held, held, failed),
                        held),
                new Derivation.ThroughABinding(failed));
    }

    /** {@code step} with every step under it, and itself, said to be an application. */
    private static Derivation appliedThroughout(Derivation step, int ordinal) {
        Derivation inner = switch (step) {
            case Derivation.IfThenElse(var condition, var then, var otherwise) ->
                    new Derivation.IfThenElse(appliedThroughout(condition, ordinal + 1),
                            appliedThroughout(then, ordinal + 2),
                            appliedThroughout(otherwise, ordinal + 3));
            case Derivation.ThroughABinding(var value) ->
                    new Derivation.ThroughABinding(appliedThroughout(value, ordinal + 1));
            default -> step;
        };
        return new Derivation.AnApplication(FOLD, ordinal, inner);
    }

    @Test
    void whatIsConcludedIsWhatTheApplicationConcludes() {
        for (Derivation step : steps()) {
            assertEquals(step.concludes(Optional.empty()),
                    appliedThroughout(step, 0).concludes(Optional.empty()), step::toString);
        }
    }

    @Test
    void aReaderOfThePremisesReachesTheApplicationsStepNext() {
        for (Derivation step : steps()) {
            Derivation applied = new Derivation.AnApplication(FOLD, 3, step);
            assertEquals(List.of(step), WrittenLines.premisesOf(applied));
            assertEquals(List.of(step), applied.oneOf(), "it states what its step states");
        }
    }

    @Test
    void anApplicationIsSomeOneOfTheCalls() {
        assertThrows(IllegalArgumentException.class,
                () -> new Derivation.AnApplication(FOLD, -1, new Derivation.Folded(true)));
        assertThrows(IllegalArgumentException.class,
                () -> new ACallOfAnOperation(FOLD.operation(), new ConstructOccurrence(
                        SourceConstructOrigin.unwritten(), OccurrenceLineage.ORIGINAL)));
    }
}
