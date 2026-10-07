package souther.compiler.inputs;

import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.StatedComparison;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.numeric.Rel;
import souther.compiler.types.Type;

import java.util.Objects;
import java.util.Optional;

/**
 * A {@code Bool} position of the input holding one of its two values, as a condition coming out a
 * way says it does.
 *
 * <p>One reading for every way of writing it. {@code a.flag}, {@code a.flag == true} and
 * {@code a.flag /= false} coming out the way that gives them say the same thing of the position,
 * and a reader that took the first and declined the others would hold one condition as two —
 * composing a row against one spelling, and saying of the other that nothing reaches it.
 *
 * @param at   the position
 * @param held which of the two values it holds
 */
public record InputTruth(TermPath at, boolean held) {

    public InputTruth {
        Objects.requireNonNull(at, "the position a truth is read at");
    }

    /**
     * What {@code cond} coming out {@code holding} says of one {@code Bool} position, or null where
     * it says nothing of one: {@code cond} is the position, or a comparison of it against a truth
     * the source settles.
     */
    public static InputTruth of(Core cond, boolean holding, InputReads reads, Symbols symbols,
                                DeclarationNewtypes newtypes) {
        TermPath at = positionOf(cond, reads, newtypes);
        if (at != null) {
            return new InputTruth(at, holding);
        }
        return BooleanMeaning.asAComparison(Core.withoutStanding(cond))
                .map(comparison -> compared(comparison, holding, reads, symbols, newtypes))
                .orElse(null);
    }

    /**
     * The position {@code e} reads a {@code Bool} at, or null where it reads none.
     *
     * <p>A truth read straight off the input, which is a value a row writes there. Anything else
     * of type {@code Bool} — what an operation answers, a comparison — is not a position, and is
     * read as what it means or declined.
     */
    public static TermPath positionOf(Core e, InputReads reads, DeclarationNewtypes newtypes) {
        return Core.withoutStanding(e).type() == Type.Prim.BOOL
                && reads.pathOf(e, newtypes) instanceof PathResolution.At(TermPath at)
                ? at : null;
    }

    /**
     * What {@code comparison} coming out {@code holding} says where it holds a {@code Bool}
     * position against a truth the source settles, or null where it does not.
     *
     * <p>Read before any order is asked for, because a {@code Bool} stands on none: the comparison
     * is the position holding one of two values, which is what reading the position as a truth
     * says ({@link #positionOf}).
     */
    public static InputTruth compared(StatedComparison comparison, boolean holding,
                                      InputReads reads, Symbols symbols,
                                      DeclarationNewtypes newtypes) {
        Rel states = comparison.claim().statedRelation();
        Rel met = holding ? states : states.denied();
        if (met != Rel.EQ && met != Rel.NE) {
            return null;
        }
        TermPath at = positionOf(comparison.left(), reads, newtypes);
        Core other = comparison.right();
        if (at == null) {
            at = positionOf(comparison.right(), reads, newtypes);
            other = comparison.left();
        }
        if (at == null) {
            return null;
        }
        Optional<Boolean> written = BooleanMeaning.folded(other, symbols);
        if (written.isEmpty()) {
            return null;
        }
        return new InputTruth(at, written.get() == (met == Rel.EQ));
    }
}
