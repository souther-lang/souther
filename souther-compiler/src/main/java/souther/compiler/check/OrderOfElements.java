package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.semantics.Combinator;
import souther.compiler.semantics.ElementShape;
import souther.compiler.semantics.HowAClosureIsApplied;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Map;

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
 * of the library reads no order of what it is handed at a place where its facts say its answer is
 * the same in any order ({@link #takenInAnyOrder}); handed a value that may hold a list anywhere
 * else, it may, and so may anything a helper, a behavior or a function value is handed beyond a
 * single number or string — what it does with it is not in this tree. Every way a run may end counts, a sum with no place among them:
 * a run that ends answers nothing and is no row of anything, whatever the reason it ended for.
 * What a closure may end a run for is {@link WhatARunMayEndFor}'s, and a closure handed by a name
 * is the block the name was given.
 *
 * <p>The rules a declaration writes on the input are not in these trees. An invariant reading the
 * order of a list, or one whose closure may answer nothing, is a form the reading of a declaration's
 * rules leaves unread, and a behavior under one is not measured; the ones it does read — how many,
 * whether some or every element meets something total, whether they are apart — read no order.
 *
 * @param read     whether something in the body may read the order a list holds its elements in
 * @param stopping how many operations stop at the first element meeting what their closure states,
 *                 where the closure may end a run or is not known not to
 */
public record OrderOfElements(boolean read, int stopping) {

    /** What is said of a body nothing was read of: that its order is read, whatever it is. */
    public static final OrderOfElements NOT_KNOWN = new OrderOfElements(true, 0);

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

    /**
     * What {@code roots}, a body and the trees of the values it builds, read, with {@code held}
     * what each name they bind was given: a closure handed by its name is the block the name was
     * given ({@link ElementBindings#blockOf}).
     */
    static OrderOfElements of(List<Core> roots, Map<BindingId, Core> held) {
        boolean[] read = {false};
        int[] stopping = {0};
        for (Core root : roots) {
            walk(root, held, read, stopping);
        }
        return new OrderOfElements(read[0], stopping[0]);
    }

    /**
     * Whether {@code applied} goes through what it is handed until its closure answers one way, and
     * its closure may end a run: what the closure ends a run for ({@link WhatARunMayEndFor}) is
     * something or not known, or the closure is no block a name was given.
     */
    private static boolean stopsAtTheFirstAndMayEndARun(AnOperationApplied applied,
                                                        Map<BindingId, Core> held) {
        Combinator rule = Combinators.of(applied.operation());
        if (rule == null || (rule.applied() != HowAClosureIsApplied.UNTIL_ONE_HOLDS
                && rule.applied() != HowAClosureIsApplied.UNTIL_ONE_FAILS)
                || rule.closureArg() >= applied.args().size()) {
            return false;
        }
        Core.Block step = ElementBindings.blockOf(applied.args().get(rule.closureArg()), held);
        return step == null || !WhatARunMayEndFor.of(step.body()).endsNone();
    }

    private static void walk(Core e, Map<BindingId, Core> held, boolean[] read, int[] stopping) {
        if (read[0]) {
            return;
        }
        Core node = Core.withoutStanding(e);
        AnOperationApplied applied = AnOperationApplied.of(node);
        if (applied != null) {
            boolean ofTheLibrary = applied.operation() instanceof ValueName.Stdlib;
            for (int at = 0; at < applied.args().size(); at++) {
                Type type = Core.withoutStanding(applied.args().get(at)).type();
                if (ofTheLibrary ? holdsAList(type) && !takenInAnyOrder(applied.operation(), at,
                        type) : !aNumberOrAString(type)) {
                    read[0] = true;
                    return;
                }
            }
            if (stopsAtTheFirstAndMayEndARun(applied, held)) {
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
        Core.forEachChild(node, child -> walk(child, held, read, stopping));
    }

    /**
     * Whether the operation {@code operation} answers the same of what it is handed at {@code at},
     * a value of {@code type}, in whatever order that holds its elements — as the library's facts
     * about it say, each held to what the library computes.
     *
     * <p>A number taken of how many it holds, or whether it holds none, is the same in any order. So
     * is a statement about its elements that survives their being put in another order
     * ({@link ElementShape#PERMUTES}): where the operation hands each element to a closure, what the
     * closure does with it is in this walk, and where it compares the elements with a value
     * itself, they are read whole, so elements that may hold a list are read in their own order.
     * Nothing else is: an operation building a list out of another hands on its order to whatever
     * reads what it built, and which elements it keeps may be the order's.
     */
    private static boolean takenInAnyOrder(ValueName operation, int at, Type type) {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        if (facts.takenAs(operation) instanceof TakenAs.HowManyItHolds
                || facts.meansTheSameAsASizeOfNought(operation) != null) {
            return true;
        }
        BoundOperationFact.ReadsItsContainer reads = facts.readsItsContainer(operation);
        if (reads == null || reads.container().position() != at
                || !reads.through().contains(ElementShape.PERMUTES)) {
            return false;
        }
        Combinator rule = Combinators.of(operation);
        return (rule != null && rule.containerArg() == at) || !elementsHoldAList(type);
    }

    /** Whether the elements of a container of {@code type} may hold a list. */
    private static boolean elementsHoldAList(Type type) {
        return switch (type) {
            case Type.ListOf(Type element) -> holdsAList(element);
            case Type.SetOf(Type element) -> holdsAList(element);
            case Type.MapOf(Type key, Type value) -> holdsAList(key) || holdsAList(value);
            default -> true;
        };
    }

    /**
     * Whether a value of {@code type} may hold a list: one the type says holds one, and one whose
     * type says nothing of what it holds here — a declared data, a union.
     *
     * <p>Not a function value: an operation applies it and reads nothing of it, and what applying it
     * reads is its body's, which this walk reads where the block is written.
     */
    private static boolean holdsAList(Type type) {
        return switch (type) {
            case Type.Prim _, Type.FnOf _ -> false;
            case Type.OptionOf(Type element) -> holdsAList(element);
            case Type.SetOf(Type element) -> holdsAList(element);
            case Type.MapOf(Type key, Type value) -> holdsAList(key) || holdsAList(value);
            case Type.TupleOf(List<Type> elements) ->
                    elements.stream().anyMatch(OrderOfElements::holdsAList);
            default -> true;
        };
    }

    /** Whether a value of {@code type} is a number, a string, a truth or a time, and so holds no
     *  container a reader handed it could go through. */
    private static boolean aNumberOrAString(Type type) {
        return type instanceof Type.Prim;
    }
}
