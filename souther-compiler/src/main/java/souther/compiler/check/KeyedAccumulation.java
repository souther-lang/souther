package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.core.WhatABodyReads;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.proof.KeyedUpdates;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.Refinement;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * A map built by walking a list from the empty map, filing under the key of each element a value
 * that starts at one figure and moves by another with every further element of that key.
 *
 * <p>Read off the fold's law and the step's, and from no name the author gave anything. The walk
 * answers the seed or the step applied to an earlier answer and an element ({@link Reductions});
 * the step files one value under one key of the answer so far and leaves every other key as it was
 * — an operation the library writes that way ({@link KeyedUpdates}), or the same written out as a
 * lookup of the key and a filing under it. So by induction over the walk the answer holds a key
 * exactly where some element of the list has it, and under it {@code first + step * (n - 1)} where
 * {@code n} is how many elements of the list have it: the first of them files {@code first}, and
 * each further one moves the value found by what the closure adds.
 *
 * <p>Of a step whose reach into the answer so far is that one update and nothing else. The key and
 * the figures it files are read of the element alone — a key that read the answer so far, or a
 * figure that turned on the element, would make the value under a key depend on what came before
 * and not on how many — and the closure moves the value by a constant, which is {@code n -> n + c}
 * in any order of writing it. A step that is anything else says nothing of what its values are.
 *
 * @param walked  the list the map is built from
 * @param element the step's parameter each element of {@code walked} arrives on
 * @param key     the key the step files an element under, a number of the element alone
 * @param first   the value filed under a key the first time an element has it
 * @param step    what a further element of the same key adds to the value
 */
public record KeyedAccumulation(Core walked, Core.Binder element, Core key, ExactRatio first,
                                ExactRatio step) {

    private static final ValueName.Stdlib.Operation EMPTY =
            ValueName.Stdlib.operation("Map", "empty");

    private static final ValueName.Stdlib.Operation GET = ValueName.Stdlib.operation("Map", "get");

    private static final ValueName.Stdlib.Operation INSERT =
            ValueName.Stdlib.operation("Map", "insert");

    /** Read once: the library is the same library for every module compiled. */
    private static final class Derived {
        private static final Map<ValueName.Stdlib.Operation, KeyedUpdates.Update> UPDATES =
                KeyedUpdates.of(DefaultStdlib.get());
    }

    /** What one step of the walk files, and under which key. */
    private record Filing(Core key, ExactRatio first, ExactRatio step) {}

    /**
     * What {@code container} is the answer of, where it is a map built so, or null where it is
     * not.
     *
     * @param blockOf the block a closure argument stands for, where the call stands
     */
    public static KeyedAccumulation of(Core container, Function<Core, Core.Block> blockOf) {
        if (!(Core.withoutStanding(container) instanceof Core.PreservedCall call)) {
            return null;
        }
        Reductions.Reducing walk = Reductions.reducing(call, blockOf);
        if (walk == null || !(AnOperationApplied.of(walk.seed()) instanceof AnOperationApplied seed)
                || !seed.operation().equals(EMPTY) || walk.element() == null
                || walk.element().binding() == null || walk.accumulator() == null
                || walk.accumulator().binding() == null) {
            return null;
        }
        BindingId accumulator = walk.accumulator().binding();
        Filing filing = filedByAnOperation(walk.step().body(), accumulator, blockOf);
        if (filing == null) {
            filing = filedAfterALookup(walk.step().body(), accumulator);
        }
        return filing == null ? null : new KeyedAccumulation(walk.container(), walk.element(),
                filing.key(), filing.first(), filing.step());
    }

    /** The filing {@code body} is, where it applies an operation that files under a key. */
    private static Filing filedByAnOperation(Core body, BindingId accumulator,
                                             Function<Core, Core.Block> blockOf) {
        if (!(AnOperationApplied.of(body) instanceof AnOperationApplied filing)
                || !(filing.operation() instanceof ValueName.Stdlib.Operation named)) {
            return null;
        }
        KeyedUpdates.Update update = Derived.UPDATES.get(named);
        if (update == null) {
            return null;
        }
        List<Core> args = filing.args();
        Core key = args.get(update.keyArg());
        ExactRatio first = constant(args.get(update.absentArg()));
        Core.Block closure = blockOf.apply(args.get(update.closureArg()));
        if (!isThe(args.get(update.mapArg()), accumulator) || WhatABodyReads.binding(key, accumulator)
                || first == null || closure == null || closure.params().size() != 1
                || closure.params().getFirst().binding() == null) {
            return null;
        }
        ExactRatio step = stepOf(closure.body(), closure.params().getFirst().binding());
        return step == null ? null : new Filing(key, first, step);
    }

    /**
     * The filing {@code body} is, where it looks the key up in the answer so far and files under
     * the key what it found moved by a constant, or a figure where it found nothing.
     */
    private static Filing filedAfterALookup(Core body, BindingId accumulator) {
        if (!(Core.withoutStanding(body) instanceof Core.Match match)
                || match.cases().size() != 2
                || !(AnOperationApplied.of(match.scrutinee()) instanceof AnOperationApplied looked)
                || !looked.operation().equals(GET) || looked.args().size() != 2
                || !isThe(looked.args().get(1), accumulator)) {
            return null;
        }
        Core key = looked.args().get(0);
        Core.Case found = armOf(match, true);
        Core.Case missing = armOf(match, false);
        if (found == null || missing == null || found.binder() == null
                || found.binder().binding() == null || WhatABodyReads.binding(key, accumulator)) {
            return null;
        }
        ExactRatio first = filedUnder(missing.body(), key, accumulator);
        ExactRatio step = stepOfWhatWasFiled(found.body(), key, accumulator,
                found.binder().binding());
        return first == null || step == null ? null : new Filing(key, first, step);
    }

    /** The arm taking an optional that holds a value, or the one taking an optional that holds
     *  none; null where there is no such arm. */
    private static Core.Case armOf(Core.Match match, boolean holdingAValue) {
        for (Core.Case each : match.cases()) {
            if (each.pattern() instanceof Core.ResolvedPattern.Single one
                    && (holdingAValue
                    ? one.selected().refinement() instanceof Refinement.OptionPresent
                    : one.selected().refinement() instanceof Refinement.OptionAbsent)) {
                return each;
            }
        }
        return null;
    }

    /** The constant {@code body} files under {@code key} in the answer so far, or null where it
     *  files anything else or files under another key. */
    private static ExactRatio filedUnder(Core body, Core key, BindingId accumulator) {
        List<Core> args = insertedInto(body, key, accumulator);
        return args == null ? null : constant(args.get(1));
    }

    /** What {@code body} adds to the value {@code found} to file under {@code key} in the answer
     *  so far, or null where it files anything else. */
    private static ExactRatio stepOfWhatWasFiled(Core body, Core key, BindingId accumulator,
                                                 BindingId found) {
        List<Core> args = insertedInto(body, key, accumulator);
        return args == null ? null : stepOf(args.get(1), found);
    }

    /** The arguments of {@code body}, where it files a value under {@code key} in the answer so
     *  far; null where it does anything else. */
    private static List<Core> insertedInto(Core body, Core key, BindingId accumulator) {
        return AnOperationApplied.of(body) instanceof AnOperationApplied filing
                && filing.operation().equals(INSERT) && filing.args().size() == 3
                && sameValue(filing.args().get(0), key)
                && isThe(filing.args().get(2), accumulator) ? filing.args() : null;
    }

    /** Whether two expressions are one value: a name, or a field read of one. */
    private static boolean sameValue(Core one, Core other) {
        Core left = Core.withoutStanding(one);
        Core right = Core.withoutStanding(other);
        if (left instanceof Core.Read read && right instanceof Core.Read there) {
            return read.binding().equals(there.binding());
        }
        return left instanceof Core.FieldAccess access && right instanceof Core.FieldAccess there
                && access.field().equals(there.field())
                && sameValue(access.target(), there.target());
    }

    /** The whole number {@code e} is written as, or null where it is no such constant. */
    private static ExactRatio constant(Core e) {
        return Core.withoutStanding(e) instanceof Core.Int written
                ? ExactRatio.of(written.value()) : null;
    }

    /**
     * What {@code body} adds to the value {@code value} it is handed, where that is a constant:
     * {@code n}, {@code n + c}, {@code c + n} and {@code n - c}.
     */
    private static ExactRatio stepOf(Core body, BindingId value) {
        Core written = Core.withoutStanding(body);
        if (isThe(written, value)) {
            return ExactRatio.ZERO;
        }
        if (!(written instanceof Core.Binary(BinOp op, Core left, Core right, var _, var _, var _,
                var _, var _))) {
            return null;
        }
        if (op == BinOp.ADD && isThe(left, value) && constant(right) != null) {
            return constant(right);
        }
        if (op == BinOp.ADD && isThe(right, value) && constant(left) != null) {
            return constant(left);
        }
        if (op == BinOp.SUB && isThe(left, value) && constant(right) != null) {
            return constant(right).negated();
        }
        return null;
    }

    private static boolean isThe(Core e, BindingId binding) {
        return Core.withoutStanding(e) instanceof Core.Read read && read.binding().equals(binding);
    }

}
