package souther.compiler.flow;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

/**
 * Whether a comparison has a value of what it is over that brings it out a given way.
 *
 * <p>Asked once per way and never as "a comparison comes out both ways". That rule reads a value
 * this reading cannot work out as a value it has worked out to be two things, and the two are what
 * this whole reading exists to keep apart: {@code a == a} comes out one way, {@code 1 > 2} comes out
 * one way, and a rule about the shape of the node would say both come out two. A way with nothing
 * standing behind it is not answered here, and the caller reads that as having nothing to say rather
 * than as the way being closed.
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
 * <p>What is not read is the model's own rules. A behavior that requires {@code a > 1} has no run
 * with a small {@code a}, and this says a way to false stands behind {@code a > 1} all the same. That
 * is the same liberty the reading of what arrives has always taken — an arm of a fork is counted
 * without anything having asked whether the condition can come out that way — and not a new one.
 */
final class Witnessed {

    /**
     * Whether a value of what is compared brings {@code comparison} out {@code want}.
     *
     * @param settledBy what a name was bound to, or null where the body bound it to nothing this can
     *                  read — a parameter, an arm's binding, a value handed in from outside
     */
    static boolean comesOut(Core.Binary comparison, boolean want,
                            Function<Core.Read, Core> settledBy) {
        Core left = comparison.left();
        Core right = comparison.right();
        List<Object> here = positionOf(left, settledBy);
        List<Object> there = positionOf(right, settledBy);
        if (here != null && there != null) {
            // Two positions nothing settles against each other: they can be given the same value
            // and they can be given different ones, so every way of every comparison stands.
            return !here.equals(there);
        }
        if (here != null) {
            return right instanceof Core.Int written && isWholeNumber(written.type())
                    && against(comparison.op(), written.value(), want);
        }
        if (there != null && left instanceof Core.Int written && isWholeNumber(written.type())) {
            return against(mirrored(comparison.op()), written.value(), want);
        }
        return false;
    }

    /**
     * Whether some whole number brings {@code position op written} out {@code want}.
     *
     * <p>Read off the ends of the range and not by trying values. What closes a way is the number
     * written being the last one on the side the way needs, which is the only thing about a range of
     * every whole number that can close one.
     */
    private static boolean against(Hir.BinOp op, long written, boolean want) {
        return switch (op) {
            // Equal to it, and every other whole number is not.
            case EQ, NE -> true;
            case GT -> !want || written < Long.MAX_VALUE;
            case GE -> want || written > Long.MIN_VALUE;
            case LT -> !want || written > Long.MIN_VALUE;
            case LE -> want || written < Long.MAX_VALUE;
            case AND, OR, ADD, SUB, MUL, DIV, CONCAT -> false;
        };
    }

    /** The same comparison written the other way round, so the number is always on the right. */
    private static Hir.BinOp mirrored(Hir.BinOp op) {
        return switch (op) {
            case LT -> Hir.BinOp.GT;
            case LE -> Hir.BinOp.GE;
            case GT -> Hir.BinOp.LT;
            case GE -> Hir.BinOp.LE;
            default -> op;
        };
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
        if (!isWholeNumber(e.type())) {
            return null;
        }
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

    private static boolean isWholeNumber(Type type) {
        return type == Type.Prim.INT;
    }

    private Witnessed() {}
}
