package souther.compiler.inputs;

import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.StatedComparison;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
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
     * the source settles — read through what {@link #asked} reads through.
     */
    public static InputTruth of(Core cond, boolean holding, InputReads reads, Symbols symbols,
                                DeclarationNewtypes newtypes) {
        Asked asked = asked(cond, holding, reads, symbols, newtypes);
        TermPath at = positionOf(asked.value(), asked.reads(), newtypes);
        if (at != null) {
            return new InputTruth(at, asked.holding());
        }
        return BooleanMeaning.asAComparison(asked.value())
                .map(comparison -> compared(comparison, asked.holding(), asked.reads(), symbols,
                        newtypes))
                .orElse(null);
    }

    /**
     * A truth as what it is asked of: the value itself, read where it stands, and which way it is
     * to come out.
     *
     * @param value   the value, standing as nothing wider
     * @param reads   what the names in it read
     * @param holding which way it is to come out
     */
    public record Asked(Core value, InputReads reads, boolean holding) { }

    /**
     * {@code truth} coming out {@code holding}, as what it is asked of: through a {@code let} to
     * its body, through a name to what it stands for, and through a denial to what it denies, the
     * other way round.
     *
     * <p>The one way through these, for every reader of what a truth is. A reader that looked
     * through some of them and not others would hold {@code Bool.not(a.flag)} as one condition and
     * {@code a.flag == false} as another.
     *
     * <p>It terminates because a binder's value can only mention binders introduced before it, and a
     * denial is smaller than what it denies.
     */
    public static Asked asked(Core truth, boolean holding, InputReads reads, Symbols symbols,
                              DeclarationNewtypes newtypes) {
        Core value = truth;
        InputReads in = reads;
        boolean way = holding;
        while (true) {
            Core e = Core.withoutStanding(value);
            if (e instanceof Core.LetIn let) {
                value = let.body();
                in = in.and(let.binder(), let.value());
                continue;
            }
            if (e instanceof Core.Read name
                    && in.meaningOf(name, symbols, newtypes) instanceof ReadMeaning.Through through) {
                value = through.denotes().value();
                in = through.denotes().at();
                continue;
            }
            Optional<BooleanMeaning.UnderADenial> denied = BooleanMeaning.underADenial(e, way);
            if (denied.isPresent()) {
                value = denied.get().part();
                way = denied.get().positive();
                continue;
            }
            return new Asked(e, in, way);
        }
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
        return BooleanMeaning.againstATruth(comparison, holding, symbols,
                        side -> positionOf(side, reads, newtypes) != null)
                .map(against -> new InputTruth(positionOf(against.side(), reads, newtypes),
                        against.held()))
                .orElse(null);
    }
}
