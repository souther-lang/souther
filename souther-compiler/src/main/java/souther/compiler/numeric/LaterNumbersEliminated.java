package souther.compiler.numeric;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What bounds on several numbers leave each of them once the numbers after it, in one order, are
 * eliminated: for each number, the bounds of it and of the numbers before it that hold wherever
 * some values of the numbers after it meet every bound given.
 *
 * <p>Exactly those, over the rationals. A bound on a sum two numbers share reaches the first of
 * them only through the second, so a closure reading one bound at a time may leave the first wider
 * than the bounds together do: {@code z + w >= 2}, {@code z + w <= 2}, {@code z - w >= 0} and
 * {@code z - w <= 0} each leave {@code z} anything, and the four leave it one. A number below one
 * bound and above another is between them only where the one is no greater than the other, which
 * is a bound without the number in it (Fourier–Motzkin elimination). So values given in the order,
 * each where the bounds at its own level leave it once the earlier ones stand at theirs, leave
 * every later number some rational value.
 *
 * <p>Not some whole value. {@code a} between one and two with {@code 2b == a} leaves {@code a}
 * both, and only two leaves {@code b} a whole number.
 *
 * <p>A bound below a number and one above it that are both of that number alone put together no
 * bound of another, only one of no number that holds or fails. They are not put together pair by
 * pair: the tightest below is set beside the tightest above, which fails exactly where any pair
 * would, and no pair is counted for it. Numbers no bound holds together are eliminated with no
 * pairs at all.
 *
 * <p>Every other pair of a bound below a number and one above it is a bound, so the bounds may
 * multiply with each number eliminated. The pairs are counted as they are put together, and the
 * elimination stops before a number that would take more than are allowed ({@link StoppedShort}).
 *
 * @param <A> what a number is called
 */
public sealed interface LaterNumbersEliminated<A> {

    /** How many pairs of bounds were put together. */
    long pairsCombined();

    /**
     * Every number eliminated after the first.
     *
     * @param levels for each number, at its place in the order, the bounds weighing it that are of
     *               it and of the numbers before it
     */
    record Eliminated<A>(List<List<Bound<A>>> levels, long pairsCombined)
            implements LaterNumbersEliminated<A> {

        public Eliminated {
            levels = List.copyOf(levels);
        }
    }

    /** No rational values meet the bounds: two of them put together leave a bound of no number
     *  that fails. */
    record NoneLeft<A>(long pairsCombined) implements LaterNumbersEliminated<A> {
    }

    /**
     * Stopped before eliminating the number at {@code place}, which says nothing of the numbers
     * before it.
     *
     * @param place   the place of the number not eliminated
     * @param reached for each number from {@code place} on, the bounds its level holds, exactly as
     *                {@link Eliminated#levels} has them
     * @param why     what stopped it
     */
    record StoppedShort<A>(int place, List<List<Bound<A>>> reached, Why why, long pairsCombined)
            implements LaterNumbersEliminated<A> {

        public StoppedShort {
            reached = List.copyOf(reached);
        }
    }

    /** What stopped an elimination short. */
    enum Why {

        /** The number would have taken more pairs than were allowed. */
        PAIRS,

        /** The exact arithmetic could not hold a bound put together. */
        ARITHMETIC
    }

    /**
     * {@code form} below nought where {@code strict}, and at or below it otherwise.
     *
     * @param <A> what a number is called
     */
    record Bound<A>(LinearForm<A> form, boolean strict) {
    }

    /**
     * What {@code bounds} leave each of {@code order} once the numbers after it are eliminated,
     * putting together no more than {@code pairs} pairs of bounds.
     *
     * @throws IllegalArgumentException where a bound weighs a number not in {@code order}
     */
    static <A> LaterNumbersEliminated<A> of(List<Bound<A>> bounds, List<A> order, long pairs) {
        Map<A, Integer> placeOf = new HashMap<>();
        for (int each = 0; each < order.size(); each++) {
            placeOf.put(order.get(each), each);
        }
        List<List<Bound<A>>> levels = new ArrayList<>();
        order.forEach(_ -> levels.add(List.of()));
        Set<Bound<A>> left = new LinkedHashSet<>();
        for (Bound<A> each : bounds) {
            if (!placeOf.keySet().containsAll(each.form().coefs().keySet())) {
                throw new IllegalArgumentException("a bound weighs a number not in the order: "
                        + each);
            }
            if (!taken(each, placeOf, left)) {
                return new NoneLeft<>(0);
            }
        }
        long combined = 0;
        for (int place = order.size() - 1; place >= 0; place--) {
            A number = order.get(place);
            List<Bound<A>> below = new ArrayList<>();
            List<Bound<A>> above = new ArrayList<>();
            Set<Bound<A>> rest = new LinkedHashSet<>();
            for (Bound<A> each : left) {
                ExactRatio weight = each.form().coefs().get(number);
                if (weight == null) {
                    rest.add(each);
                } else {
                    (weight.signum() > 0 ? above : below).add(each);
                }
            }
            List<Bound<A>> level = new ArrayList<>(below);
            level.addAll(above);
            levels.set(place, List.copyOf(level));
            Bound<A> floor = null;
            Bound<A> ceiling = null;
            for (Bound<A> each : below) {
                floor = each.form().coefs().size() == 1 ? tighter(floor, each) : floor;
            }
            for (Bound<A> each : above) {
                ceiling = each.form().coefs().size() == 1 ? tighter(ceiling, each) : ceiling;
            }
            if (floor != null && ceiling != null) {
                LinearForm<A> between = between(ceiling.form(), floor.form(), number);
                if (between == null) {
                    return new StoppedShort<>(place, levels.subList(place, levels.size()),
                            Why.ARITHMETIC, combined);
                }
                if (!taken(new Bound<>(between, floor.strict() || ceiling.strict()), placeOf,
                        rest)) {
                    return new NoneLeft<>(combined);
                }
            }
            if (place == 0) {
                break;
            }
            long alone = below.stream().filter(each -> each.form().coefs().size() == 1).count()
                    * above.stream().filter(each -> each.form().coefs().size() == 1).count();
            long these = (long) below.size() * above.size() - alone;
            if (these > pairs - combined) {
                return new StoppedShort<>(place, levels.subList(place, levels.size()), Why.PAIRS,
                        combined);
            }
            for (Bound<A> up : above) {
                for (Bound<A> down : below) {
                    if (up.form().coefs().size() == 1 && down.form().coefs().size() == 1) {
                        continue;
                    }
                    combined++;
                    LinearForm<A> between = between(up.form(), down.form(), number);
                    if (between == null) {
                        return new StoppedShort<>(place, levels.subList(place, levels.size()),
                                Why.ARITHMETIC, combined);
                    }
                    if (!taken(new Bound<>(between, up.strict() || down.strict()), placeOf,
                            rest)) {
                        return new NoneLeft<>(combined);
                    }
                }
            }
            left = rest;
        }
        return new Eliminated<>(levels, combined);
    }

    /**
     * The tighter of two bounds of one number alone, both normalised so the number weighs one
     * either way round: the greater constant leaves the number less room, and of two at the same
     * constant, the strict one does.
     */
    private static <A> Bound<A> tighter(Bound<A> one, Bound<A> other) {
        if (one == null) {
            return other;
        }
        int by = one.form().constant().compareTo(other.form().constant());
        return by != 0 ? by > 0 ? one : other : other.strict() ? other : one;
    }

    /**
     * What {@code up}, weighing {@code number} above nought, and {@code down}, weighing it below,
     * leave without it: each scaled by the other's weight so the two weights cancel, and added — or
     * null where the exact arithmetic cannot hold that.
     */
    private static <A> LinearForm<A> between(LinearForm<A> up, LinearForm<A> down, A number) {
        ExactRatio above = up.coefs().get(number);
        ExactRatio below = down.coefs().get(number).negated();
        LinearForm<A> upScaled = up.times(below).orNull();
        LinearForm<A> downScaled = down.times(above).orNull();
        return upScaled == null || downScaled == null ? null
                : upScaled.plus(downScaled).orNull();
    }

    /**
     * Adds {@code bound} to {@code into}, divided through by the weight of the latest number it is
     * of so that one bound written at two scales is added once — or, where it is of no number,
     * answers whether it holds and adds nothing.
     */
    private static <A> boolean taken(Bound<A> bound, Map<A, Integer> placeOf, Set<Bound<A>> into) {
        LinearForm<A> form = bound.form();
        if (form.coefs().isEmpty()) {
            int sign = form.constant().signum();
            return bound.strict() ? sign < 0 : sign <= 0;
        }
        A latest = null;
        for (A each : form.coefs().keySet()) {
            if (latest == null || placeOf.get(each) > placeOf.get(latest)) {
                latest = each;
            }
        }
        LinearForm<A> scaled = form.dividedBy(form.coefs().get(latest).abs()).orNull();
        into.add(scaled == null ? bound : new Bound<>(scaled, bound.strict()));
        return true;
    }
}
