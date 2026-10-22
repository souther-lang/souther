package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.core.WhatABodyReads;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.proof.KeyedUpdates;
import souther.compiler.semantics.HowAClosureIsApplied;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.Refinement;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * A map built by walking a list from the empty map, filing under the key of each element a value
 * worked out of what was filed under that key before.
 *
 * <p>Read off the fold's law and the step's, and from no name the author gave anything. The walk
 * answers the seed or the step applied to an earlier answer and an element ({@link Reductions});
 * the step files one value under one key of the answer so far and leaves every other key as it was
 * — an operation the library writes that way ({@link KeyedUpdates}), or the same written out as a
 * lookup of the key and a filing under it. Of a walk that applies its step to every element
 * ({@link HowAClosureIsApplied#TO_EVERY_ELEMENT}), so by induction over it the answer holds a key
 * exactly where some element of the list has it, and what it holds there is what {@link Filed}
 * says the elements of that key come to.
 *
 * <p>Of a step whose reach into the answer so far is that one update and nothing else. The key is
 * read of the element alone — a key that read the answer so far would make where an element is
 * filed depend on what came before — and what is filed is one of the {@link Filed} shapes. A step
 * that is anything else says nothing of what its values are.
 *
 * @param walked  the list the map is built from
 * @param element the step's parameter each element of {@code walked} arrives on
 * @param key     the key the step files an element under, a number of the element alone
 * @param filed   what the map holds under a key, out of the elements that have it
 */
public record KeyedAccumulation(Core walked, Core.Binder element, Core key, Filed filed) {

    public KeyedAccumulation {
        Objects.requireNonNull(filed, "a map built so holds something under each of its keys");
    }

    /**
     * What a map built so holds under a key, out of the elements of the list that have it.
     *
     * <p>Sealed, and one arm per law the value under a key follows: a reader asking what the value
     * is has to say what it is under each.
     */
    public sealed interface Filed {

        /**
         * {@code first + step * (n - 1)}, where {@code n} is how many elements have the key: the
         * first of them files {@code first}, and each further one moves the value found by what
         * the closure adds. Of a figure that does not turn on the element, and a closure moving
         * the value by a constant, which is {@code n -> n + c} in any order of writing it.
         *
         * @param first the value filed under a key the first time an element has it
         * @param step  what a further element of the same key adds to the value
         */
        record Counted(ExactRatio first, ExactRatio step) implements Filed {}

        /**
         * The least or the greatest of what {@code value} is for the elements that have the key:
         * the first of them files its value, and each further one files the end of its own value
         * and the one found that the closure keeps ({@link Extreme}).
         *
         * <p>That end only where what the closure compares the value found against is the value
         * filed first, as {@link Summed} is a total only where what it adds is: a closure comparing
         * against something else would file the first element's value on a law the rest do not
         * follow. Whether {@code compared} and {@code value} are one number of each element is the
         * element's reader's to say, for the reason it is there.
         *
         * @param value    what each element files, read of the element
         * @param compared every value the closure answers or compares that is not the value found,
         *                 as written: each is to be the same number of the element as {@code value}
         * @param extreme  which end of its own value and the one found a further element keeps
         * @param found    the name the step gives the value found under the key, which is that end
         *                 of the values of the earlier elements of the same key
         */
        record Kept(Core value, List<Core> compared, Extreme extreme, BindingId found)
                implements Filed {

            public Kept {
                Objects.requireNonNull(value, "an element files a value");
                compared = List.copyOf(compared);
                Objects.requireNonNull(extreme, "and one end of two of them is kept");
                Objects.requireNonNull(found, "of what the step finds under the key");
            }
        }

        /**
         * The total of what {@code value} is for the elements that have the key: the first of them
         * files its value, and each further one adds {@code added} to the value found.
         *
         * <p>That total only where {@code value} and {@code added} are one number of each element,
         * which is a question about the element and not about the names this reads: the two are
         * often written twice, as two calls of one helper, and two copies of a call are two
         * expressions. So both are held, and the reader of the element asks it ({@code
         * Pullback}); one that cannot read them as one number reads no total.
         *
         * @param value what the first element of a key files, read of the element
         * @param added what each further one adds to the value found, read of the element
         * @param found the name the step gives the value found under the key
         */
        record Summed(Core value, Core added, BindingId found) implements Filed {

            public Summed {
                Objects.requireNonNull(value, "an element files a value");
                Objects.requireNonNull(added, "and a further one adds one");
                Objects.requireNonNull(found, "to what the step finds under the key");
            }
        }
    }

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
    private record Filing(Core key, Filed filed) {}

    /**
     * The map {@code applied} reads a key of, where it is a lookup in it or an operation the
     * library writes that files under a key of it — or null where it is neither.
     */
    public static Core mapOf(AnOperationApplied applied) {
        if (applied.operation().equals(GET)) {
            return applied.args().size() == 2 ? applied.args().get(1) : null;
        }
        KeyedUpdates.Update update = applied.operation() instanceof ValueName.Stdlib.Operation named
                ? Derived.UPDATES.get(named) : null;
        return update == null ? null : applied.args().get(update.mapArg());
    }

    /**
     * What {@code container}, read in {@code at}, is the answer of, where it is a map built so, or
     * null where it is not.
     *
     * <p>Every part of the step is read where the reader reads names
     * ({@link TheSignOfAnOrder.Sides#standing}): what the step answers, which operation files and
     * into what, whether the key reads the answer so far, and what the closure keeps of two values.
     * So a step is the same filing however what it answers is named. The key and the value filed
     * are kept as they are written, since a reader of them reads them as numbers of the element
     * the step is handed, which is a name the reading of names would follow past.
     *
     * @param sides   what the reader answers about where it reads
     * @param blockOf the block a closure argument stands for, where the call stands
     * @param <E>     what the reader reads a name in
     */
    public static <E> KeyedAccumulation of(Core container, E at, TheSignOfAnOrder.Sides<E> sides,
                                           Function<Core, Core.Block> blockOf) {
        if (!(Core.withoutStanding(container) instanceof Core.PreservedCall call)) {
            return null;
        }
        Reductions.Reducing walk = Reductions.reducing(call, blockOf);
        if (walk == null || walk.applied() != HowAClosureIsApplied.TO_EVERY_ELEMENT
                || !(AnOperationApplied.of(sides.standing(walk.seed(), at).value())
                instanceof AnOperationApplied seed)
                || !seed.operation().equals(EMPTY) || walk.element() == null
                || walk.element().binding() == null || walk.accumulator() == null
                || walk.accumulator().binding() == null) {
            return null;
        }
        AStep<E> step = new AStep<>(walk.accumulator().binding(), sides, blockOf);
        ValueStanding.ReadThrough<E> body = sides.standing(walk.step().body(), at);
        Filing filing = step.byAnOperation(body);
        if (filing == null) {
            filing = step.afterALookup(body);
        }
        return filing == null ? null : new KeyedAccumulation(walk.container(), walk.element(),
                filing.key(), filing.filed());
    }

    /**
     * A step of the walk, read where the reader reads names.
     *
     * @param accumulator the step's parameter the answer so far arrives on
     * @param sides       what the reader answers about where it reads
     * @param blockOf     the block a closure argument stands for
     */
    private record AStep<E>(BindingId accumulator, TheSignOfAnOrder.Sides<E> sides,
                            Function<Core, Core.Block> blockOf) {

        /** What {@code e}, read in {@code at}, was given: past every name it was given. */
        Core valueOf(Core e, E at) {
            return sides.standing(e, at).value();
        }

        /** The filing {@code body} is, where it applies an operation that files under a key. */
        Filing byAnOperation(ValueStanding.ReadThrough<E> body) {
            if (!(AnOperationApplied.of(body.value()) instanceof AnOperationApplied filing)
                    || !(filing.operation() instanceof ValueName.Stdlib.Operation named)) {
                return null;
            }
            KeyedUpdates.Update update = Derived.UPDATES.get(named);
            if (update == null) {
                return null;
            }
            List<Core> args = filing.args();
            Core key = args.get(update.keyArg());
            Core.Block closure = blockOf.apply(args.get(update.closureArg()));
            if (!isThe(valueOf(args.get(update.mapArg()), body.at()), accumulator)
                    || WhatABodyReads.binding(valueOf(key, body.at()), accumulator)
                    || closure == null || closure.params().size() != 1
                    || closure.params().getFirst().binding() == null) {
                return null;
            }
            Filed filed = filedOf(args.get(update.absentArg()), body.at(),
                    sides.standing(closure.body(), body.at()),
                    closure.params().getFirst().binding());
            return filed == null ? null : new Filing(key, filed);
        }

        /**
         * The filing {@code body} is, where it looks the key up in the answer so far and files
         * under the key what it worked out of what it found, or a figure where it found nothing.
         */
        Filing afterALookup(ValueStanding.ReadThrough<E> body) {
            if (!(Core.withoutStanding(body.value()) instanceof Core.Match match)
                    || match.cases().size() != 2
                    || !(AnOperationApplied.of(valueOf(match.scrutinee(), body.at()))
                    instanceof AnOperationApplied looked)
                    || !looked.operation().equals(GET) || looked.args().size() != 2
                    || !isThe(valueOf(looked.args().get(1), body.at()), accumulator)) {
                return null;
            }
            Core key = looked.args().get(0);
            Core keyRead = valueOf(key, body.at());
            Core.Case found = armOf(match, true);
            Core.Case missing = armOf(match, false);
            if (found == null || missing == null || found.binder() == null
                    || found.binder().binding() == null
                    || WhatABodyReads.binding(keyRead, accumulator)) {
                return null;
            }
            ValueStanding.ReadThrough<E> first =
                    filedUnder(sides.standing(missing.body(), body.at()), keyRead);
            ValueStanding.ReadThrough<E> moved =
                    filedUnder(sides.standing(found.body(), body.at()), keyRead);
            Filed filed = first == null || moved == null ? null
                    : filedOf(first.value(), first.at(), moved, found.binder().binding());
            return filed == null ? null : new Filing(key, filed);
        }

        /**
         * What the map holds under a key where an element finding nothing there files
         * {@code first}, read in {@code firstAt}, and one finding {@code found} there files
         * {@code moved} — or null where that is neither a counter nor an end kept.
         */
        Filed filedOf(Core first, E firstAt, ValueStanding.ReadThrough<E> moved,
                      BindingId found) {
            Core firstRead = valueOf(first, firstAt);
            ExactRatio figure = constant(firstRead);
            ExactRatio step = figure == null ? null : stepOf(moved, found);
            if (step != null) {
                return new Filed.Counted(figure, step);
            }
            if (WhatABodyReads.binding(firstRead, accumulator)) {
                return null;
            }
            Core added = addedTo(moved, found, first, firstAt);
            if (added != null) {
                return new Filed.Summed(first, added, found);
            }
            List<Choice.ADefinitionCase> cases =
                    Extreme.casesOf(moved.value(), moved.at(), sides);
            Predicate<Core> isFound =
                    e -> isThe(Extreme.comparedAs(e, moved.at(), sides).value(), found);
            Extreme extreme = Extreme.keptBy(cases, isFound, isFound.negate());
            List<Core> compared = Extreme.besides(cases, isFound);
            for (Core each : compared) {
                Core read = valueOf(each, moved.at());
                if (WhatABodyReads.binding(read, found)
                        || WhatABodyReads.binding(read, accumulator)) {
                    return null;
                }
            }
            return extreme == null ? null : new Filed.Kept(first, compared, extreme, found);
        }

        /** The value {@code body} files under the key read as {@code key} in the answer so far, as
         *  written and where it is written — or null where it does anything else or files under
         *  another key. */
        ValueStanding.ReadThrough<E> filedUnder(ValueStanding.ReadThrough<E> body, Core key) {
            return AnOperationApplied.of(body.value()) instanceof AnOperationApplied filing
                    && filing.operation().equals(INSERT) && filing.args().size() == 3
                    && Core.sameValue(valueOf(filing.args().get(0), body.at()), key)
                    && isThe(valueOf(filing.args().get(2), body.at()), accumulator)
                    ? new ValueStanding.ReadThrough<>(filing.args().get(1), body.at()) : null;
        }

        /**
         * What {@code moved} adds to the value {@code found} it is handed, where it is that value
         * once and a sum of things read of no other — or null where it is anything else.
         *
         * <p>Read as the arithmetic reads it ({@link TheSignOfAnOrder.Sides#overTheCalls}), so
         * how the sum is grouped and in which order it is written say nothing: {@code n + a + b},
         * {@code n + (a + b)} and {@code a + n + b} add the same, and an operation the library says
         * computes an addition adds as {@code +} does. What it adds is the one value it adds where
         * it adds one, and {@code first} — what an element finding nothing files — where it adds
         * the same sum of values as that is.
         */
        Core addedTo(ValueStanding.ReadThrough<E> moved, BindingId found, Core first, E firstAt) {
            LinearForm<AffineForms.ACall<E>> stepped =
                    sides.overTheCalls(moved.value(), moved.at(), leaf -> true);
            if (stepped == null) {
                return null;
            }
            List<Weighed> stepping = weighed(stepped);
            if (stepping == null) {
                return null;
            }
            List<Weighed> rest = new ArrayList<>();
            boolean once = false;
            for (Weighed each : stepping) {
                if (isThe(each.value(), found)) {
                    if (each.by().compareTo(ExactRatio.ONE) != 0) {
                        return null;
                    }
                    once = true;
                } else if (WhatABodyReads.binding(each.value(), found)
                        || WhatABodyReads.binding(each.value(), accumulator)) {
                    return null;
                } else {
                    rest.add(each);
                }
            }
            if (!once) {
                return null;
            }
            if (stepped.constant().signum() == 0 && rest.size() == 1
                    && rest.getFirst().by().compareTo(ExactRatio.ONE) == 0) {
                return rest.getFirst().written();
            }
            LinearForm<AffineForms.ACall<E>> filed =
                    sides.overTheCalls(first, firstAt, leaf -> true);
            List<Weighed> filing = filed == null ? null : weighed(filed);
            return filing != null && stepped.constant().compareTo(filed.constant()) == 0
                    && sameSum(rest, filing) ? first : null;
        }

        /**
         * One value a sum adds, as written and as what it is read as, and how many times it adds
         * it in all.
         */
        private record Weighed(Core written, Core value, ExactRatio by) {}

        /**
         * The values {@code form} adds, each once with every weight it is written at added up —
         * two places a sum writes one value at are that value added twice — or null where the
         * weights cannot be held.
         */
        private List<Weighed> weighed(LinearForm<AffineForms.ACall<E>> form) {
            List<Weighed> out = new ArrayList<>();
            for (Map.Entry<AffineForms.ACall<E>, ExactRatio> each : form.coefs().entrySet()) {
                Core value = valueOf(each.getKey().call(), each.getKey().at());
                int at = -1;
                for (int i = 0; i < out.size(); i++) {
                    if (Core.sameValue(out.get(i).value(), value)) {
                        at = i;
                    }
                }
                if (at < 0) {
                    out.add(new Weighed(each.getKey().call(), value, each.getValue()));
                    continue;
                }
                ExactRatio summed = out.get(at).by().plus(each.getValue()).orNull();
                if (summed == null) {
                    return null;
                }
                out.set(at, new Weighed(out.get(at).written(), value, summed));
            }
            out.removeIf(each -> each.by().signum() == 0);
            return out;
        }

        /** Whether {@code one} and {@code other} add the same values, each as many times. */
        private static boolean sameSum(List<Weighed> one, List<Weighed> other) {
            if (one.size() != other.size()) {
                return false;
            }
            for (Weighed each : one) {
                if (other.stream().noneMatch(there -> Core.sameValue(each.value(), there.value())
                        && each.by().compareTo(there.by()) == 0)) {
                    return false;
                }
            }
            return true;
        }

        /**
         * What {@code moved} adds to the value {@code value} it is handed, where that is a
         * constant: {@code n}, {@code n + c}, {@code c + n} and {@code n - c}.
         */
        ExactRatio stepOf(ValueStanding.ReadThrough<E> moved, BindingId value) {
            Core written = Core.withoutStanding(moved.value());
            if (isThe(written, value)) {
                return ExactRatio.ZERO;
            }
            if (!(written instanceof Core.Binary(BinOp op, Core l, Core r, var _, var _, var _,
                    var _, var _))) {
                return null;
            }
            Core left = valueOf(l, moved.at());
            Core right = valueOf(r, moved.at());
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

    /** The whole number {@code e} is written as, or null where it is no such constant. */
    private static ExactRatio constant(Core e) {
        return Core.withoutStanding(e) instanceof Core.Int written
                ? ExactRatio.of(written.value()) : null;
    }

    private static boolean isThe(Core e, BindingId binding) {
        return Core.withoutStanding(e) instanceof Core.Read read && read.binding().equals(binding);
    }

}
