package souther.compiler.partition;

import souther.compiler.coverage.ControlPlace;
import souther.compiler.inputs.SearchRegion;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Predicate;

/**
 * What a row has to be for one condition of the body to come out one way where the body reaches
 * it.
 *
 * <p>Something a row is held to beside the classes it is composed for, and never one of them. What
 * the row is for is the classes; this is what it takes to get the row past a condition that
 * stopped it.
 *
 * <p>A demand and the way to the condition, and nothing about what the condition is. How the
 * demand was arrived at — a point of a comparison's border found by searching, or what an
 * operation's answer asks of the value it was asked of — is the producer's, so what composes a row
 * against these composes it against {@link RowDemand}s whichever condition stopped the row.
 *
 * <p><b>The way as it was taken, and not only what it came to.</b> Where a condition on the way —
 * the one held or one above it — is one of several ways, which of them this is held along is said
 * by the condition it is of ({@link #chosen}), over the way whole ({@link #way}). That is what
 * carries to a guard below: the way to it takes the same conditions in, and a row held past the
 * one above along one of its ways is held past the one below along the same
 * ({@link #along(List, SearchRegion)}). What the way comes to for a composer ({@link #reaching})
 * says every vocabulary of the way but not which choice made it, so two choices that ask alike in
 * one vocabulary and apart in another could not be told from it.
 *
 * @param demands  what the row has to be for the condition to come out that way: every thing it
 *                 asks, which for a point of a border is the point and for an operation's truth
 *                 may be several at once — some element meeting a predicate, and what the
 *                 predicate asks of the rest of the row beside it
 * @param cases    which case a value is, where the condition coming out that way says so: asked
 *                 of the row as the way's requirements, which is where a composer meets them, and
 *                 here as well because holding a row to them writes the value there
 * @param way      the way to the condition and the condition coming out that way, every condition
 *                 of several ways on it as it stands
 * @param chosen   which alternative each condition of several ways on {@code way} is taken as,
 *                 by the condition; one not named here is left as it stands
 * @param reaching {@code way} taken along {@code chosen}, as a composer reads it — and, where a
 *                 demand is one a condition makes ({@link RowDemand.OfACondition}), the condition
 *                 itself, which a composer meets the way it meets every condition on the way
 */
public record HeldOutcome(List<RowDemand> demands, List<OnTheWay.Narrowed> cases,
                          WayToTheBorder way, Map<OnTheWay, Integer> chosen,
                          Reachability.Reaching reaching) {

    public HeldOutcome {
        demands = List.copyOf(demands);
        cases = List.copyOf(cases);
        Objects.requireNonNull(way, "the way to the condition");
        Objects.requireNonNull(reaching, "the way as a composer reads it");
        chosen = Collections.unmodifiableMap(new LinkedHashMap<>(chosen));
        if (demands.isEmpty() && cases.isEmpty()) {
            throw new IllegalArgumentException(
                    "a condition held to coming out a way asks something of the row");
        }
    }

    /**
     * The way to the last of {@code held}, along the ways the ones before it were held along: the
     * last one's way taken along every choice any of them made — or empty where two of them took
     * one condition two ways, or the way taken so is one no row takes.
     *
     * <p>The way to a later guard takes the earlier ones in, so each choice made past an earlier
     * one is a choice of a condition on the later one's way, and it is taken there as it was. Asked
     * of the choices and not of what the ways came to: two choices asking alike of one vocabulary
     * — the same element of the same container, under two cases of one value — are two ways all
     * the same.
     *
     * @param declarations what the declarations leave, which the way narrows
     */
    static Optional<Reachability.Reaching> along(List<HeldOutcome> held,
                                                 SearchRegion declarations) {
        HeldOutcome last = held.getLast();
        Map<OnTheWay, Integer> chosen = new LinkedHashMap<>();
        for (HeldOutcome each : held) {
            for (Map.Entry<OnTheWay, Integer> one : each.chosen().entrySet()) {
                Integer before = chosen.putIfAbsent(one.getKey(), one.getValue());
                if (before != null && !before.equals(one.getValue())) {
                    return Optional.empty();
                }
            }
        }
        // Only the choices of conditions the last way takes in. A way to a comparison read
        // through several copies holds what every copy's way holds, and a condition one copy is
        // reached without is no condition of it to take a way of.
        List<OnTheWay> onIt = last.way().stated();
        chosen.keySet().retainAll(onIt);
        if (chosen.equals(last.chosen())) {
            return Optional.of(last.reaching());
        }
        return Reachability.of(last.way().choosing(chosen), declarations)
                instanceof Reachability.Reaching taken ? Optional.of(taken) : Optional.empty();
    }

    /**
     * What holds each condition of one behavior, asked for one condition at a time.
     *
     * <p>Asked rather than handed over whole. Working one out can be a search for a place, and the
     * conditions a generation asks about are the few a row stopped at.
     *
     * <p>By where a run through the condition is recorded and which way it is to come out, because
     * that is what a run is checked against: what got a row past a guard is the condition coming
     * out the way the guard needs, which is false as often as true — under
     * {@code Bool.not(x <= 0)} it is {@code x <= 0} failing. Where that is recorded is a place a
     * comparison or an application comes out a way, or for a truth no construct of its own
     * records, the arm a fork on it takes.
     */
    @FunctionalInterface
    public interface Of {

        /** What brings a run to {@code place}, or why nothing does. */
        Bringing at(ControlPlace place);

        /** Nothing holds any condition — what a caller with no borders to read uses. */
        Of NOTHING = _ -> new Bringing.NothingFound();
    }

    /**
     * What brings a run to one place, or why nothing does.
     *
     * <p>Three ways of nothing and they are not one. No value standing on the side a comparison
     * comes out on, or no row taking the way to it, is the model's: no row goes that way, and
     * none was looked for because there is none. Nothing found is this compiler's: a row may well
     * go that way, and what to hold it to was not worked out. And a figure stopping the looking is
     * this compiler's with a number somebody can raise.
     *
     * <p><b>Nothing is never read off a list being empty.</b> Where the ways of holding a row are
     * several, which of the three answers a list that came to none is depends on why each way went
     * — and on whether every way was looked at — so it is answered here ({@link #oneOf},
     * {@link Found#keeping}) and nowhere else.
     */
    public sealed interface Bringing {

        /**
         * What the row has to be: one of {@code ways}, and never all of them at once.
         *
         * <p>Several where what the condition coming out that way states is one of several things
         * — some element of one container meeting its closure or some element of another meeting
         * its own — and each of them is a way of its own, with the way to the condition taken
         * along the same alternative. Held to all of them at once, a row would be held to a
         * conjunction the condition never stated.
         *
         * @param ways     one or more, in the order they are best looked for in
         * @param cutShort the figure that left some way out, where one did: then a row past none of
         *                 these may still be past the condition, and saying no way goes past would
         *                 be saying more than was looked at
         */
        record Found(List<HeldOutcome> ways, Optional<CompositionBudget> cutShort)
                implements Bringing {

            public Found {
                ways = List.copyOf(ways);
                if (ways.isEmpty()) {
                    throw new IllegalArgumentException("what brings a run somewhere is some way");
                }
                Objects.requireNonNull(cutShort, "the figure that left a way out, or none");
            }

            /**
             * The ways {@code kept} keeps: those, where any are left; where none is and some
             * way was left out by a figure, that — since a way never looked at may be one it
             * keeps; and only where every way was looked at, none.
             */
            public Kept keeping(Predicate<HeldOutcome> kept) {
                List<HeldOutcome> left = ways.stream().filter(kept).toList();
                if (!left.isEmpty()) {
                    return new Kept.Some(new Found(left, cutShort));
                }
                return cutShort.<Kept>map(Kept.NoneLookedAtWas::new).orElseGet(Kept.None::new);
            }
        }

        /** What {@link Found#keeping} came to. */
        sealed interface Kept {

            /** These are kept. */
            record Some(Found kept) implements Kept {}

            /** None of the ways looked at is kept, and {@code figure} left some unlooked at. */
            record NoneLookedAtWas(CompositionBudget figure) implements Kept {}

            /** Every way was looked at, and none is kept. */
            record None() implements Kept {}
        }

        /**
         * The ways a row could be held to it were more than {@code figure} lets be looked at, and
         * none was found before it stopped the looking. This compiler's, as nothing found is, and
         * with the figure, which is a number somebody can raise.
         */
        record LeftUnlooked(CompositionBudget figure) implements Bringing {

            public LeftUnlooked {
                Objects.requireNonNull(figure, "the figure that stopped the looking");
            }
        }

        /**
         * No value can stand on the side the comparison comes out on, or no row takes the way to
         * it coming out so, and so nothing does.
         */
        record NoValueCanStandThere() implements Bringing {}

        /** Nothing was found that does, which does not make it a place no run comes to. */
        record NothingFound() implements Bringing {}

        /**
         * What several ways of bringing a run to one place come to together, where a run past
         * any one of them is there: every way any of them found, with the first figure any of them
         * met; where none found one, the figure, if one stopped some looking; otherwise nothing
         * found, if this compiler worked any of them out short; and only where every one of them
         * is one no row takes, that.
         *
         * <p>The one law for it. A caller putting the answers together itself would read a way
         * it gave up on as one no row takes, or a way a figure stopped as one this compiler could
         * not hold a row to.
         */
        static Bringing oneOf(List<Bringing> each) {
            List<HeldOutcome> ways = new ArrayList<>();
            Optional<CompositionBudget> figure = Optional.empty();
            boolean workedOutShort = each.isEmpty();
            for (Bringing one : each) {
                switch (one) {
                    case Found(var found, var cutShort) -> {
                        ways.addAll(found);
                        figure = figure.or(() -> cutShort);
                    }
                    case LeftUnlooked(var stopped) -> figure = figure.or(() -> Optional.of(stopped));
                    case NothingFound _ -> workedOutShort = true;
                    case NoValueCanStandThere _ -> { }
                }
            }
            if (!ways.isEmpty()) {
                return new Found(ways, figure);
            }
            if (figure.isPresent()) {
                return new LeftUnlooked(figure.get());
            }
            return workedOutShort ? new NothingFound() : new NoValueCanStandThere();
        }
    }
}
