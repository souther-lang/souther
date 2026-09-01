package souther.compiler.flow;

import souther.compiler.check.Comparison;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.core.Core;
import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

/**
 * Whether a value of what an expression is over brings it out a given way.
 *
 * <p>Asked once per way and never as "a comparison comes out both ways". That rule reads a value
 * this reading cannot work out as a value it has worked out to be two things, and the two are what
 * this whole reading exists to keep apart: {@code a == a} comes out one way, {@code 1 > 2} comes out
 * one way, and a rule about the shape of the node would say both come out two. A way with nothing
 * standing behind it is not answered here, and the caller reads that as having nothing to say rather
 * than as the way being closed.
 *
 * <p>Asked of an expression and not of a comparison, because what is being asked is whether a value
 * stands behind a way and that is not a question about which node kind is written. A position of the
 * input that holds a truth is such a value on its own: {@code flag} comes out both ways for the same
 * reason {@code a > b} does, and reading it as a value this cannot work out would answer that
 * {@code flag && abort} arrives nowhere while every run with a false {@code flag} arrives.
 *
 * <p>What stands behind a way is a value of the position the comparison is over, so the two sides
 * have to be positions this can name a range for and positions that do not settle each other. Such a
 * position is a name nothing settled, together with whatever is reached from one by taking fields and
 * elements of it: {@code total.value} is as free as {@code total} is.
 *
 * <p>Read through the names the body bound, because a name is not a position. A helper spliced into a
 * body binds the call's argument to the helper's own parameter, so the {@code total} inside it is the
 * caller's {@code total} and is free for the same reason that one is; a name bound to a number
 * written out is settled by that number and is not a position at all. Which of the two a name is is
 * what the resolver answers, and nothing here works it out from how the name was spelled.
 *
 * <p>Whole numbers only. A range is what a way is witnessed against, and the ranges this can be sure
 * of without asking the model anything are the primitive's. A position whose type is a data
 * declaration has whatever range that declaration was written with, which is not read here — so
 * nothing is claimed about it. Under-reading, and the direction this reading takes everywhere.
 *
 * <p>What is not read here is the model's own rules. A behavior that requires {@code a > 1} has no
 * run with a small {@code a}, and this says a way to false stands behind {@code a > 1} all the same.
 * That is what this reading is: the body's own text, and nothing that has to be looked up. A caller
 * holding the rules answers the same question of the number instead ({@link ComparisonWays}), and
 * this is what is left for the comparisons no such number is named for.
 */
final class Witnessed {

    /**
     * Whether a value of what is compared brings {@code comparison} out {@code want}.
     *
     * @param settledBy what a name was bound to, or null where the body bound it to nothing this can
     *                  read — a parameter, an arm's binding, a value handed in from outside
     */
    static boolean comesOut(Core e, boolean want, Function<Core.Read, Core> settledBy) {
        if (e instanceof Core.Binary binary) {
            Comparison comparison = Comparison.of(binary).orElse(null);
            if (comparison != null) {
                return standsBehind(binary, comparison.claim(), want, settledBy);
            }
        }
        // A position holding a truth, which can be given either of them. An operator that puts
        // comparisons together or answers a number reads as no position at all, and is answered
        // here rather than being a case of its own.
        return e.type() == Type.Prim.BOOL && positionOf(e, settledBy) != null;
    }

    /** Whether a value of what {@code comparison} is over brings what it {@code placed} out
     *  {@code want}. */
    private static boolean standsBehind(Core.Binary comparison, ComparisonClaim placed,
                                        boolean want, Function<Core.Read, Core> settledBy) {
        Core left = comparison.left();
        Core right = comparison.right();
        List<Object> here = wholeNumberPosition(left, settledBy);
        List<Object> there = wholeNumberPosition(right, settledBy);
        if (here != null && there != null) {
            // Two positions nothing settles against each other: they can be given the same value
            // and they can be given different ones, so every way of every comparison stands.
            return !here.equals(there);
        }
        if (here != null) {
            return right instanceof Core.Int written && isWholeNumber(written.type())
                    && against(placed, written.value(), want);
        }
        if (there != null && left instanceof Core.Int written && isWholeNumber(written.type())) {
            // The position on the left, which is the statement turned round and not another one.
            return against(placed.turned(), written.value(), want);
        }
        return false;
    }

    /**
     * Whether some whole number stands to {@code written} a way that brings what was
     * {@code placed} out {@code want}.
     *
     * <p>Two questions, and only the second is this reading's. Which ways a comparison comes out
     * {@code want} is what the relation it states answers ({@link Rel#holds}); whether the numbers
     * hold anything standing that way is what a range of every whole number can say, and the number
     * written being the last one on a side is the only thing that closes it.
     */
    private static boolean against(ComparisonClaim placed, long written, boolean want) {
        Rel states = placed.statedRelation();
        for (int sign = -1; sign <= 1; sign++) {
            if (states.holds(sign) == want && standsThatWay(sign, written)) {
                return true;
            }
        }
        return false;
    }

    /** Whether the whole numbers hold one standing {@code sign} from {@code written}, which the
     *  number itself always is. */
    private static boolean standsThatWay(int sign, long written) {
        if (sign == 0) {
            return true;
        }
        return sign < 0 ? written > Long.MIN_VALUE : written < Long.MAX_VALUE;
    }

    /**
     * Which position of the input {@code e} reads, or null where it reads none this can be sure of.
     *
     * <p>The name at the root, after every name the body settled has been read through, and what was
     * taken out of it — which together are what says whether two of these are the same position. Two that are equal are settled by one value, so nothing about a
     * comparison between them varies; two that differ are settled by two, and every way of every
     * comparison between them has a value behind it.
     */
    private static List<Object> positionOf(Core e, Function<Core.Read, Core> settledBy) {
        List<Object> taken = new ArrayList<>();
        Core at = e;
        while (true) {
            switch (at) {
                case Core.FieldAccess access -> {
                    taken.add(access.field());
                    at = access.target();
                }
                case Core.TupleGet get -> {
                    taken.add(get.index());
                    at = get.tuple();
                }
                case Core.Read read -> {
                    Core to = settledBy.apply(read);
                    if (to != null) {
                        at = to;
                        continue;
                    }
                    taken.add(read.binding());
                    java.util.Collections.reverse(taken);
                    return taken;
                }
                default -> {
                    return null;
                }
            }
        }
    }

    /** The position {@code e} reads where it holds a whole number, and null otherwise. */
    private static List<Object> wholeNumberPosition(Core e, Function<Core.Read, Core> settledBy) {
        return isWholeNumber(e.type()) ? positionOf(e, settledBy) : null;
    }

    private static boolean isWholeNumber(Type type) {
        return type == Type.Prim.INT;
    }

    private Witnessed() {}
}
