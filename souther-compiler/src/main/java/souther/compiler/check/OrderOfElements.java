package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Set;

/**
 * Whether a body reads the order its lists hold their elements in, and how many of its operations
 * stop at the first element meeting a statement that may answer nothing on some rows.
 *
 * <p>For a reading that answers what such an operation comes to without saying which element a run
 * reaches first ({@code souther.compiler.meaning.HowTheElementsAreAsked}). A row holding an element
 * that meets the statement holds it first too, written in another order — the same row to
 * everything else the body asks of it, where nothing else the body asks turns on the order. So
 * whether some row comes out meeting it is what the runs say, and that is all the reading claims.
 * Two such operations over one list are not: one may need an element first that the other needs
 * second, and neither run answers. And one statement that reads the order makes a row in one order
 * a different row from the same elements in another.
 *
 * <p>Read off what the body writes, and kept on the side of saying the order is read. An operation
 * the library defines in terms of how many elements meet something, or what each is mapped to, or
 * what they add up to, reads no order; every other one handed a list may, and so may anything a
 * helper, a behavior or a function value is handed beyond a single number or string — what it does
 * with it is not in this tree. Whether a closure may answer nothing is {@link WhatMayStopARun}'s.
 *
 * <p>The rules a declaration writes on the input are not in these trees. An invariant reading the
 * order of a list, or one whose closure may answer nothing, is a form the reading of a declaration's
 * rules leaves unread, and a behavior under one is not measured; the ones it does read — how many,
 * whether some or every element meets something total, whether they are apart — read no order.
 *
 * @param read     whether something in the body may read the order a list holds its elements in
 * @param stopping how many operations stop at the first element meeting what their closure states,
 *                 where what it states may answer nothing on some rows
 */
public record OrderOfElements(boolean read, int stopping) {

    /** What is said of a body nothing was read of: that its order is read, whatever it is. */
    public static final OrderOfElements NOT_KNOWN = new OrderOfElements(true, 0);

    /** The operations over a list whose answer is the same in whatever order it holds them. */
    private static final Set<ValueName> IN_ANY_ORDER = Set.of(
            ValueName.Stdlib.operation("List", "any"),
            ValueName.Stdlib.operation("List", "all"),
            ValueName.Stdlib.operation("List", "length"),
            ValueName.Stdlib.operation("List", "isEmpty"),
            ValueName.Stdlib.operation("List", "contains"),
            ValueName.Stdlib.operation("List", "sum"),
            ValueName.Stdlib.operation("List", "product"),
            ValueName.Stdlib.operation("List", "max"),
            ValueName.Stdlib.operation("List", "min"),
            ValueName.Stdlib.operation("List", "sort"),
            ValueName.Stdlib.operation("List", "filter"),
            ValueName.Stdlib.operation("List", "map"),
            ValueName.Stdlib.operation("List", "append"),
            ValueName.Stdlib.operation("List", "allDistinctBy"),
            ValueName.Stdlib.operation("Set", "fromList"));

    /** Of those, the ones that stop at the first element their closure answers one way on. */
    private static final Set<ValueName> STOPPING = Set.of(
            ValueName.Stdlib.operation("List", "any"),
            ValueName.Stdlib.operation("List", "all"));

    public OrderOfElements {
        if (stopping < 0) {
            throw new IllegalArgumentException("operations are counted from nought: " + stopping);
        }
    }

    /** What two bodies read together, one read where the other calls it. */
    public OrderOfElements and(OrderOfElements other) {
        return new OrderOfElements(read || other.read, stopping + other.stopping);
    }

    /**
     * Whether the one operation stopping at the first element meeting a statement that may answer
     * nothing is read in an order the rows choose: nothing else reads an order, and no other such
     * operation stands beside it.
     */
    public boolean leftToTheRows() {
        return !read && stopping <= 1;
    }

    /** What {@code roots}, a body and the trees of the values it builds, read. */
    public static OrderOfElements of(List<Core> roots) {
        boolean[] read = {false};
        int[] stopping = {0};
        for (Core root : roots) {
            walk(root, read, stopping);
        }
        return new OrderOfElements(read[0], stopping[0]);
    }

    private static void walk(Core e, boolean[] read, int[] stopping) {
        if (read[0]) {
            return;
        }
        Core node = Core.withoutStanding(e);
        AnOperationApplied applied = AnOperationApplied.of(node);
        if (applied != null) {
            boolean ofTheLibrary = applied.operation() instanceof ValueName.Stdlib;
            for (Core argument : applied.args()) {
                Type type = Core.withoutStanding(argument).type();
                if (ofTheLibrary ? holdsAList(type) && !IN_ANY_ORDER.contains(applied.operation())
                        : !aNumberOrAString(type)) {
                    read[0] = true;
                    return;
                }
            }
            // A closure handed by a name is a body this walk does not go into here, and may stop.
            if (STOPPING.contains(applied.operation()) && applied.args().stream()
                    .anyMatch(argument -> argument.type() instanceof Type.FnOf
                            && (!(Core.withoutStanding(argument) instanceof Core.Block step)
                                    || WhatMayStopARun.in(step.body())))) {
                stopping[0]++;
            }
        }
        // A function value, or a call this walk names no operation of, is a body this tree does not
        // hold; and two values holding lists are the same value only where their elements stand
        // in the same order.
        if ((node instanceof Core.Apply apply && apply.args().stream()
                .anyMatch(argument -> !aNumberOrAString(argument.type())))
                || (applied == null && node instanceof Core.Call call && call.args().stream()
                        .anyMatch(argument -> !aNumberOrAString(argument.type())))
                || (node instanceof Core.Binary binary
                        && (binary.op() == BinOp.EQ || binary.op() == BinOp.NE)
                        && !aNumberOrAString(binary.left().type()))) {
            read[0] = true;
            return;
        }
        Core.forEachChild(node, child -> walk(child, read, stopping));
    }

    /** Whether a value of {@code type} holds a list anywhere a reader can tell from the type. */
    private static boolean holdsAList(Type type) {
        if (type instanceof Type.ListOf) {
            return true;
        }
        if (type instanceof Type.OptionOf(Type element)) {
            return holdsAList(element);
        }
        if (type instanceof Type.SetOf(Type element)) {
            return holdsAList(element);
        }
        if (type instanceof Type.MapOf(Type key, Type value)) {
            return holdsAList(key) || holdsAList(value);
        }
        return type instanceof Type.TupleOf(List<Type> elements)
                && elements.stream().anyMatch(OrderOfElements::holdsAList);
    }

    /** Whether a value of {@code type} is a number, a string, a truth or a time, and so holds no
     *  container a reader handed it could go through. */
    private static boolean aNumberOrAString(Type type) {
        return type instanceof Type.Prim;
    }
}
