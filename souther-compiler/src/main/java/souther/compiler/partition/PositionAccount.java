package souther.compiler.partition;

import souther.compiler.inputs.Position;
import souther.compiler.inputs.StructuralInspection;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.Type;

/**
 * One position of a behavior's input, and what this phase is left answering for at it.
 *
 * <p>Held once for the position and pointed at by every axis on it, because a position is measured
 * at as many numbers as the rules name of it and none of what is here is one of those numbers.
 * Where the walk stopped, what the reading of the declarations left standing, and what the position
 * is if nothing answers are facts about the location — true of it once, whether it is measured at
 * its own content, at how long it is, or at both.
 *
 * <p><b>What this replaces was the same facts stored on the measure.</b> That said nothing false
 * while there was one measure per position, and it made two questions look like one: whether a
 * position is still waiting on something was asked through the axis standing at it
 * ({@link PendingPosition}), which is an answer about the location arrived at through whichever
 * number it happened to be measured by.
 *
 * <p>An axis holds one of these rather than a copy of what is in it. A copy per measure is a fact
 * with as many representations as the position has numbers, and the first of them to be rebuilt
 * without one of its parts is the one a report reads — which is what {@link ReadingResidue} was
 * written to catch one field at a time.
 *
 * @param pending  where nothing has answered for this position yet, what the structural reading
 *                 found — and so what the position is left with if nothing else answers. Null where
 *                 the reading of the declarations already answered, which needs no fallback
 * @param leftWith what the position is left with where the local reading gave it no axis, or null
 *                 where nothing is. Which of the two it is comes with it: a reading stopped, or a
 *                 rule was read to the end and draws no line. Kept apart from {@link #pending}
 *                 because the two are lifted by different work and one outranks the other — where
 *                 the walk could not reach into what the position holds, a rule about what is
 *                 inside describes that same stop from the other end
 */
public record PositionAccount(TermPath path, Type type, ReadingResidue residue,
                              StructuralInspection.Continuation pending,
                              LeftAtThePosition leftWith) {

    public PositionAccount {
        if (residue == null) {
            throw new IllegalArgumentException(
                    "a position with no account of what its reading came to");
        }
    }

    /** What one position's reading came to, as the reading itself answered it. */
    public static PositionAccount of(Position position,
                                     StructuralInspection.Continuation pending,
                                     LeftAtThePosition leftWith) {
        return new PositionAccount(position.path(), position.type(),
                ReadingResidue.of(position), pending, leftWith);
    }

    /** A position outside a reading of the declarations, which is where a test writes one. */
    static PositionAccount at(TermPath path, Type type) {
        return new PositionAccount(path, type, ReadingResidue.NOTHING, null, null);
    }
}
