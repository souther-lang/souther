package souther.compiler.partition;

import souther.compiler.coverage.ControlPlace;
import souther.compiler.inputs.SearchRegion;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.TreeSet;
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
 * @param chosen   which alternatives each condition of several ways on {@code way} is taken as,
 *                 by the condition ({@link #byCondition}) — every one a row along the way meets;
 *                 one not named here is left as it stands
 * @param reaching {@code way} taken along {@code chosen}, as a composer reads it — and, where a
 *                 demand is one a condition makes ({@link RowDemand.OfACondition}), the condition
 *                 itself, which a composer meets the way it meets every condition on the way
 */
public record HeldOutcome(List<RowDemand> demands, List<OnTheWay.Narrowed> cases,
                          WayToTheBorder way, Map<OnTheWay, Set<Integer>> chosen,
                          Reachability.Reaching reaching) {

    public HeldOutcome {
        demands = List.copyOf(demands);
        cases = List.copyOf(cases);
        Objects.requireNonNull(way, "the way to the condition");
        Objects.requireNonNull(reaching, "the way as a composer reads it");
        Map<OnTheWay, Set<Integer>> copied = new LinkedHashMap<>();
        chosen.forEach((condition, alternatives) -> {
            if (alternatives.isEmpty()) {
                throw new IllegalArgumentException("a condition chosen is taken some way: "
                        + condition);
            }
            copied.put(condition, Collections.unmodifiableSet(new TreeSet<>(alternatives)));
        });
        chosen = Collections.unmodifiableMap(copied);
        if (demands.isEmpty() && cases.isEmpty()) {
            throw new IllegalArgumentException(
                    "a condition held to coming out a way asks something of the row");
        }
    }

    /**
     * The choices a walk made along one way, as the conditions they are of: each condition with
     * every alternative of it the way took.
     *
     * <p>Two identities, and this is where one becomes the other. The walk chooses by where an
     * entry stands, and two entries alike standing at two places are two choices
     * ({@link OneOfEach.Choice}); what a way past one guard carries to the next is which
     * condition was taken which way, and the way to the next reads the same condition as an entry
     * of its own, alike and not the same object. So a condition is the entry as the reading
     * states it, and two choices of it are two alternatives a row along the way meets at once.
     */
    static Map<OnTheWay, Set<Integer>> byCondition(List<OneOfEach.Choice<OnTheWay>> made) {
        Map<OnTheWay, Set<Integer>> out = new LinkedHashMap<>();
        for (OneOfEach.Choice<OnTheWay> each : made) {
            out.computeIfAbsent(each.entry(), _ -> new TreeSet<>()).add(each.alternative());
        }
        return out;
    }

    /**
     * The way to the last of {@code held}, along the ways the ones before it were held along: the
     * last one's way taken along every choice any of them made — or why no row takes it so.
     *
     * <p>The way to a later guard takes the earlier ones in, so each choice made past an earlier
     * one is a choice of a condition on the later one's way, and it is taken there as it was. Asked
     * of the choices and not of what the ways came to: two choices asking alike of one vocabulary
     * — the same element of the same container, under two cases of one value — are two ways all
     * the same.
     *
     * <p>Where two of them took one condition two ways, the row is held to both alternatives, and
     * whether a row is both is what reading the way says: two containers each holding an element
     * that meets its predicate is a way, and a value two cases at once is none
     * ({@link WayToTheBorder#choosing}).
     *
     * <p>And not the last way alone. A row held past a guard above is held to everything that way
     * asked, what it chose and what it did not; the way to a later guard usually takes all of that
     * in, but a way to a comparison read through several copies holds only what every copy's way
     * holds, and a condition one copy is reached without is not on it. So the way taken is every
     * one of them, each along the choices made, each condition once: what a row has to be to be
     * past every guard it was held past and at the last, and nothing told apart by which of them
     * happened to say it.
     *
     * @param declarations what the declarations leave, which the way narrows
     */
    static Reachability along(List<HeldOutcome> held, SearchRegion declarations) {
        if (held.size() == 1) {
            return held.getFirst().reaching();
        }
        Map<OnTheWay, Set<Integer>> chosen = new LinkedHashMap<>();
        for (HeldOutcome each : held) {
            each.chosen().forEach((condition, alternatives) -> chosen
                    .computeIfAbsent(condition, _ -> new TreeSet<>()).addAll(alternatives));
        }
        Set<OnTheWay> entries = new LinkedHashSet<>();
        for (HeldOutcome each : held) {
            entries.addAll(each.way().choosing(chosen).onTheWay());
        }
        return Reachability.of(new WayToTheBorder(List.copyOf(entries)), declarations);
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
         * @param cutShort the figures that left some way out, none where every way is here: where
         *                 any did, a row past none of these may still be past the condition, and
         *                 saying no way goes past would be saying more than was looked at. Every
         *                 one of them, since each is a number somebody would have to raise
         */
        record Found(List<HeldOutcome> ways, Set<CompositionBudget> cutShort)
                implements Bringing {

            public Found {
                ways = List.copyOf(ways);
                if (ways.isEmpty()) {
                    throw new IllegalArgumentException("what brings a run somewhere is some way");
                }
                cutShort = InDeclaredOrder.of(cutShort);
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
                return cutShort.isEmpty() ? new Kept.None() : new Kept.NoneLookedAtWas(cutShort);
            }
        }

        /** What {@link Found#keeping} came to. */
        sealed interface Kept {

            /** These are kept. */
            record Some(Found kept) implements Kept {}

            /** None of the ways looked at is kept, and {@code figures} left some unlooked at. */
            record NoneLookedAtWas(Set<CompositionBudget> figures) implements Kept {

                public NoneLookedAtWas {
                    figures = InDeclaredOrder.of(figures);
                    if (figures.isEmpty()) {
                        throw new IllegalArgumentException("ways left unlooked at were left by"
                                + " some figure");
                    }
                }
            }

            /** Every way was looked at, and none is kept. */
            record None() implements Kept {}
        }

        /**
         * The ways a row could be held to it were more than {@code figures} let be looked at, and
         * none was found before they stopped the looking. This compiler's, as nothing found is,
         * and with the figures, which are numbers somebody can raise.
         */
        record LeftUnlooked(Set<CompositionBudget> figures) implements Bringing {

            public LeftUnlooked {
                figures = InDeclaredOrder.of(figures);
                if (figures.isEmpty()) {
                    throw new IllegalArgumentException("the looking was stopped by some figure");
                }
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
         * any one of them is there: every way any of them found, with every figure any of them
         * met; where none found one, the figures, if any stopped some looking; otherwise nothing
         * found, if this compiler worked any of them out short; and only where every one of them
         * is one no row takes, that.
         *
         * <p>The one law for it. A caller putting the answers together itself would read a way
         * it gave up on as one no row takes, or a way a figure stopped as one this compiler could
         * not hold a row to.
         */
        static Bringing oneOf(List<Bringing> each) {
            List<HeldOutcome> ways = new ArrayList<>();
            Set<CompositionBudget> figures = EnumSet.noneOf(CompositionBudget.class);
            boolean workedOutShort = each.isEmpty();
            for (Bringing one : each) {
                switch (one) {
                    case Found(var found, var cutShort) -> {
                        ways.addAll(found);
                        figures.addAll(cutShort);
                    }
                    case LeftUnlooked(var stopped) -> figures.addAll(stopped);
                    case NothingFound _ -> workedOutShort = true;
                    case NoValueCanStandThere _ -> { }
                }
            }
            if (!ways.isEmpty()) {
                return new Found(ways, figures);
            }
            if (!figures.isEmpty()) {
                return new LeftUnlooked(figures);
            }
            return workedOutShort ? new NothingFound() : new NoValueCanStandThere();
        }
    }
}
