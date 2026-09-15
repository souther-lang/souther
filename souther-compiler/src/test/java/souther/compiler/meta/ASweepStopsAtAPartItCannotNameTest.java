package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Type;
import java.util.List;
import java.util.SequencedSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A sweep over what a declaration reaches stops at a part it cannot name, rather than reading it as
 * a part that holds nothing.
 *
 * <p>The two read the same to a sweep and mean opposite things. A part that holds nothing is one a
 * sweep is finished with; a part nothing here can name is one a sweep has not looked at, and a sweep
 * that walks past it reaches less and stays green — which is the failure the sweeps above exist to
 * catch and the one they would then be having. So an unnamed part stops the sweep and says so.
 *
 * <p>Held here and not in the sweeps, because a sweep cannot witness it: nothing a declaration
 * reaches today is written that way, and a sweep can only show what it did reach. What it would do
 * on meeting one is asked of the reading directly.
 */
class ASweepStopsAtAPartItCannotNameTest {

    @Test
    void aPartWrittenToHoldWhateverItsFormWasMadeWithStopsTheSweep() {
        assertThrows(IllegalStateException.class,
                () -> TypesAPartIsDeclaredToHold.named(partOf(Holds.class, "value")),
                "a part written to hold whatever the form was made with names no type to go on"
                        + " from, and a sweep that passed it over would say nothing about it");
    }

    @Test
    void andSoDoesOneWrittenToHoldAnythingOfAKind() {
        assertThrows(IllegalStateException.class,
                () -> TypesAPartIsDeclaredToHold.named(partOf(Holds.class, "some")),
                "nor does a part written to hold anything of a kind");
    }

    /**
     * The control: a container written as what it holds is read through, whichever of them it is.
     *
     * <p>Without it the refusals above would be met by a reading that refused everything, and the
     * sweeps would stop at their first part. A sequenced set is here because it is what caught this:
     * the reading named the four containers it knew and read a fifth as a part holding nothing, and
     * what that fifth holds went unswept.
     */
    @Test
    void whileAContainerIsReadThroughHoweverItIsWritten() {
        assertEquals(List.of(String.class),
                TypesAPartIsDeclaredToHold.named(partOf(Holds.class, "many")),
                "a list is read through");
        assertEquals(List.of(String.class),
                TypesAPartIsDeclaredToHold.named(partOf(Holds.class, "ordered")),
                "and so is a set written as the kind of set it is");
    }

    /** Stands for the ways a part can be written. */
    @SuppressWarnings("unused")
    private record Holds<T>(T value, Set<? extends CharSequence> some, List<String> many,
                            SequencedSet<String> ordered) {}

    /** The declared type of one part of {@code form}. */
    private static Type partOf(Class<?> form, String part) {
        for (StructuralParts.Part each : StructuralParts.of(form)) {
            if (each.name().equals(part)) {
                return each.held();
            }
        }
        throw new IllegalStateException("no part `" + part + "` of " + form.getName());
    }
}
