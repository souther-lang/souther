package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.CanonicalOrder;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.ConstantArguments;
import souther.compiler.semantics.ResultRange;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * A comparison of the number an operation answering the order of its two arguments answered, read
 * as what it states of those two arguments.
 *
 * <p>What such an operation answers is a sign
 * ({@link BoundOperationFacts#statesTheOrderOfItsArguments(ValueName)}), so a comparison that
 * settles which side of nought the answer falls on is a comparison of the argument a positive
 * answer names as the greater against the other one.
 *
 * <p><b>One account for every reader of a condition.</b> Which side of the comparison is the sign,
 * which way round the relation is read from it, what the other side is, and which relation of the
 * arguments that comes to are all answered here, and a reader says only what is particular to its
 * own environment ({@link Sides}). A reader answering any of them itself is a second account of one
 * comparison, and two readers of a condition — one following a name given the sign to the
 * operation behind it and one not — read it two ways.
 *
 * <p>Composed in the numeric domain rather than decided here, so that what a step is worth is the
 * step the domain knows about: over whole numbers {@code > -1} is {@code >= 0}, and this would
 * either have to say so a second time or answer as though a sign could fall between the two. The
 * rules taken in are the two there are — what the operation declares of its answer and what the
 * comparison says.
 */
public final class TheSignOfAnOrder {

    private TheSignOfAnOrder() {}

    /**
     * What a reader answers about its own environment, and nothing else.
     *
     * @param <E> the environment the reader reads an expression in
     */
    public interface Sides<E> {

        /** What {@code e} stands for where it is read — a name followed to what it was given — and
         *  the environment that is read in; {@code e} itself where it is no name. */
        AffineForms.ReadThrough<E> standing(Core e, E at);

        /** The number {@code e} is on every run, or null where it is none. */
        ExactRatio constant(Core e, E at);

        /** What a type is declared as, for how the values of the sign are spaced. */
        DeclarationAccess declarations();
    }

    /**
     * What a comparison of a sign states of the arguments.
     *
     * @param <E> the environment the arguments are read in
     */
    public sealed interface Read<E> {

        /** What the sign was compared with: the answer counted at {@code spacing}, standing
         *  {@code written} to {@code against}, which is what is read off it. */
        TheSign sign();

        /**
         * The comparison of the two arguments, read where the operation was applied.
         *
         * @param isTheCondition whether the arguments standing so is exactly where the comparison
         *                       of the sign holds, and not only something it proves. A sign held
         *                       above nought by {@code compare(a, b) > 0} is {@code a > b}; a count
         *                       of days held above one by {@code daysBetween(a, b) > 1} proves
         *                       {@code b > a} and is not where it holds
         */
        record OfTheArguments<E>(TheSign sign, StatedComparison arguments, E at,
                                 boolean isTheCondition) implements Read<E> {

            public OfTheArguments {
                Objects.requireNonNull(sign, "an order is answered by an operation");
                Objects.requireNonNull(arguments, "and is of its arguments");
                Objects.requireNonNull(at, "read somewhere");
            }

            /** The operation answering the order. */
            public ValueName operation() {
                return sign.operation();
            }
        }

        /**
         * The same whatever the arguments: every answer the operation can give comes out one way
         * ({@link TheSignOfAnOrder#settledByItsBounds}), so the comparison states no order of them.
         */
        record Settled<E>(TheSign sign) implements Read<E> {

            public Settled {
                Objects.requireNonNull(sign, "an order is answered by an operation");
            }

            /** The operation answering the order. */
            public ValueName operation() {
                return sign.operation();
            }
        }
    }

    /** The answer of {@code operation}, counted at {@code spacing}, standing {@code written} to
     *  {@code against}. */
    public record TheSign(ValueName operation, Granularity spacing, Rel written,
                          ExactRatio against) {

        public TheSign {
            Objects.requireNonNull(operation, "a sign is what an operation answers");
            Objects.requireNonNull(spacing, "counted at some spacing");
            Objects.requireNonNull(written, "standing some way");
            Objects.requireNonNull(against, "to some number");
        }
    }

    /**
     * What {@code comparison}, read in {@code at}, states of the arguments of the operation one of
     * its sides is the sign of — or null where neither side is such a sign, the other side is no
     * number the same on every run, or the two rules leave the arguments open.
     */
    public static <E> Read<E> read(StatedComparison comparison, E at, Sides<E> sides) {
        for (boolean signFirst : List.of(true, false)) {
            AffineForms.ReadThrough<E> sign =
                    sides.standing(signFirst ? comparison.left() : comparison.right(), at);
            Core answered = Core.withoutStanding(sign.value());
            AnOperationApplied applied = AnOperationApplied.of(answered);
            BoundOperationFact.StatesTheOrderOfItsArguments order = applied == null ? null
                    : DefaultBoundOperationFacts.get()
                            .statesTheOrderOfItsArguments(applied.operation());
            if (order == null) {
                continue;
            }
            Core greater = applied.argument(order.greater());
            Core lesser = applied.argument(order.lesser());
            Carrier counted = Carrier.ofValue(answered.type(), sides.declarations());
            ExactRatio against =
                    sides.constant(signFirst ? comparison.right() : comparison.left(), at);
            if (greater == null || lesser == null || counted == null || !counted.counts()
                    || against == null) {
                return null;
            }
            // The relation the source wrote, read from the sign's side: `sign rel number` however
            // the two were written round.
            Rel written = (signFirst ? comparison.claim() : comparison.claim().turned())
                    .statedRelation();
            TheSign compared = new TheSign(applied.operation(), counted.spacing(), written,
                    against);
            return switch (of(applied.operation(), counted.spacing(), written, against)) {
                case null -> null;
                case Stands.Settled _ -> new Read.Settled<>(compared);
                case Stands.Between(Rel between, boolean isTheCondition) ->
                        new Read.OfTheArguments<>(compared,
                                new StatedComparison(ComparisonClaim.stating(between), greater,
                                        lesser,
                                        // Two arguments of the operation that orders them, each
                                        // standing as what it was passed as, and the order is the
                                        // one over that type.
                                        Core.BinaryReading.AS_THEY_STAND),
                                sign.at(), isTheCondition);
            };
        }
        return null;
    }

    /**
     * The relation the greater argument of {@code operation} stands in to the lesser exactly where
     * its answer, counted at {@code spacing}, stands {@code rel} to {@code against} — or null where
     * the two rules leave that open, settle it whatever the arguments are, or prove an order
     * without being where it holds.
     */
    public static Rel betweenTheArguments(ValueName operation, Granularity spacing, Rel rel,
                                          ExactRatio against) {
        return of(operation, spacing, rel, against) instanceof Stands.Between(Rel between,
                boolean isTheCondition) && isTheCondition ? between : null;
    }

    /**
     * Which way the answer of {@code operation}, counted at {@code spacing}, comes out standing
     * {@code rel} to {@code against} whatever the arguments are — or null where it is not the same
     * on every answer the library says the operation can give.
     */
    public static Boolean settledByItsBounds(ValueName operation, Granularity spacing, Rel rel,
                                             ExactRatio against) {
        return of(operation, spacing, rel, against) instanceof Stands.Settled(boolean holds)
                ? holds : null;
    }

    /** What the sign standing a way to a number states of the arguments. */
    sealed interface Stands {

        /** The greater argument stands {@code relation} to the other, exactly where the comparison
         *  holds or only wherever it does. */
        record Between(Rel relation, boolean isTheCondition) implements Stands {

            public Between {
                Objects.requireNonNull(relation, "two arguments stand in some relation");
            }
        }

        /** Every answer comes out {@code holds}. */
        record Settled(boolean holds) implements Stands {}
    }

    /** The answers of a sign on one side of nought. */
    private enum Side {

        BELOW(Rel.LT, -1), AT(Rel.EQ, 0), ABOVE(Rel.GT, 1);

        /** The answers on this side, as a relation to nought. */
        private final Rel toNought;
        /** The sign each of them has. */
        private final int sign;

        Side(Rel toNought, int sign) {
            this.toNought = toNought;
            this.sign = sign;
        }
    }

    /**
     * What the answer of {@code operation}, counted at {@code spacing}, standing {@code rel} to
     * {@code against} states of its two arguments — or null where the two rules leave it open.
     */
    static Stands of(ValueName operation, Granularity spacing, Rel rel, ExactRatio against) {
        // One atom, standing for the number the operation answered. Nothing else is in this domain:
        // what is asked is what the operation and the comparison prove between them, and a rule
        // about anything else would be a rule about a value that is not the sign.
        Object sign = new Object();
        Map<Object, Granularity> spacings = Map.of(sign, spacing);
        LinearForm<Object> answered = LinearForm.atom(sign);
        // One position, so the order is total on the domain by there being nothing to put in an
        // order. Two of them reaching it would be a second position in a domain written to have
        // one, and it says so rather than choosing between them.
        CanonicalOrder<Object> order = (one, other) -> {
            if (one == other) {
                return 0;
            }
            throw new IllegalStateException("this domain stands for one number and was asked to"
                    + " walk two: " + one + " and " + other);
        };
        NumericDomain<Object> declared = NumericDomain.top(order)
                .assuming(sign, ResultRange.of(DefaultBoundOperationFacts.get()
                        .boundsOnTheResult(operation), ConstantArguments.none()), spacings);
        ExactAnswer<LinearForm<Object>> compared = answered.minus(LinearForm.constant(against));
        if (!(compared instanceof ExactAnswer.Held<LinearForm<Object>>(LinearForm<Object> form))) {
            return null;
        }
        NumericDomain<Object> known = declared.assume(form, rel, spacings);
        if (known.isBottom()) {
            return new Stands.Settled(false);
        }
        // Asked of each side of nought apart. Where the comparison holds on every answer of a side
        // or on none, what it states is which sides it holds on, and that is a relation of the
        // arguments exactly. Asked of the whole at once, a sign held away from nought is two
        // intervals the domain holds as one, and `!= 0` would prove nothing about the order it is.
        List<Side> holds = new ArrayList<>();
        boolean failsSomewhere = false;
        boolean decided = true;
        for (Side side : Side.values()) {
            NumericDomain<Object> there = declared.assume(answered, side.toNought, spacings);
            if (there.isBottom()) {
                continue;
            }
            if (there.entails(form, rel)) {
                holds.add(side);
            } else if (there.assume(form, rel, spacings).isBottom()) {
                failsSomewhere = true;
            } else {
                decided = false;
            }
        }
        if (decided && !failsSomewhere) {
            return new Stands.Settled(true);
        }
        // Tightest first: a sign held at nought is an equality and not two half-statements, and one
        // held above it says more than one held at or above it. The first that covers every side
        // the comparison holds on is those sides and no other, since each one side and each two
        // of them is one of these, so it covers none it fails on.
        for (Rel each : List.of(Rel.EQ, Rel.GT, Rel.LT, Rel.GE, Rel.LE, Rel.NE)) {
            if (decided && holds.stream().allMatch(side -> each.holds(side.sign))) {
                return new Stands.Between(each, true);
            }
        }
        // A side the comparison holds on only some of: what it proves of the order is all that is
        // left to say, and that is not where it holds.
        for (Rel each : List.of(Rel.EQ, Rel.GT, Rel.LT, Rel.GE, Rel.LE, Rel.NE)) {
            if (known.entails(answered, each)) {
                return new Stands.Between(each, false);
            }
        }
        return null;
    }
}
