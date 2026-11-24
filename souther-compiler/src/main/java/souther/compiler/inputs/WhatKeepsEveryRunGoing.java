package souther.compiler.inputs;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * The declarations that together keep every run getting to a rule from taking a number past where
 * its type stops in what the rule works out: one region of the input, as the invariants an author
 * declares make it. Within all of them no run stops so there. A stop of any other kind, such as a
 * construction on the way refusing what it is handed, is none of what this keeps a run from.
 *
 * <p>Said of what the invariants are declared on, and not of the places of the input: a data's
 * invariant holds every value of it, so two places one data holds are bounded by one declaration,
 * the tighter of what each asks, and the region is the declarations whatever order they were met
 * in.
 *
 * <p>Made only where each data keeps a value under them: what every reading says its rules and its
 * type already leave it ({@code held}), met with both sides declared, holds a whole number. What
 * one reading says is what a value of the input holds at every place the declarations hold, one
 * number at each, all together ({@code AValueOfTheInput}); readings put together keep what each
 * says, so the region is beside all of them. Bounds only tighten and accounts only narrow as
 * readings are put together, so a region that leaves some data no value stays one however many
 * more are put in, and none is the answer whatever order they are put in.
 *
 * <p>How far out the region goes is a second fact, said of each bound apart: a bound is as far out
 * as one can be where a run with it declared one step further out, every other declaration
 * holding, is shown to stop ({@code asFarOutAsCanBe}). That is a claim about the region, so it is
 * made once the region is whole and never of a bound alone. It is shown by one reading, of a run
 * of the input that reading reads, so it rests on the declarations and on nothing another reading
 * says a holder is left: an account of another input that leaves the holder less is no account of
 * the input the run was of, and takes nothing from the run.
 *
 * <p>That a value of the input holds every declaration at once is shown by a reading over the
 * places its own declarations hold ({@code shownTogether}), and is a third fact, kept apart from
 * the bounds: readings put together hold every one of theirs, and the region is said only where
 * one of them holds all it declares on ({@link #heldTogether}), which is asked once every reading
 * of the rule is put together, whatever order they came in.
 *
 * @param bounds          the declarations, each data and side once
 * @param held            what every reading put together says each data a bound is declared on is
 *                        already left, every one of which is a value: of exactly the data the
 *                        bounds are declared on
 * @param asFarOutAsCanBe the bounds of {@code bounds} as far out as one can be
 * @param shownTogether   each set of what is declared on that a value of the input was shown to
 *                        hold at once, every combination of what its rules leave the places of
 *                        each being held
 */
public record WhatKeepsEveryRunGoing(Set<ABoundThatKeepsEveryRunGoing> bounds,
                                     Map<ABoundThatKeepsEveryRunGoing.Holder,
                                             ABoundThatKeepsEveryRunGoing.Held> held,
                                     Set<ABoundThatKeepsEveryRunGoing> asFarOutAsCanBe,
                                     Set<Set<ABoundThatKeepsEveryRunGoing.Holder>> shownTogether) {

    public WhatKeepsEveryRunGoing {
        bounds = Collections.unmodifiableSequencedSet(new LinkedHashSet<>(bounds));
        held = Map.copyOf(held);
        asFarOutAsCanBe = Set.copyOf(asFarOutAsCanBe);
        shownTogether = shownTogether.stream().map(Set::copyOf)
                .collect(Collectors.toUnmodifiableSet());
        if (!held.keySet().equals(bounds.stream().map(ABoundThatKeepsEveryRunGoing::holder)
                .collect(Collectors.toSet()))) {
            throw new IllegalArgumentException("what is held is said of the data the bounds are"
                    + " declared on: " + bounds + " " + held.keySet());
        }
        if (bounds.stream().map(ABoundThatKeepsEveryRunGoing::side).distinct().count()
                != bounds.size() || !keepsEveryDataAValue(bounds, held)) {
            throw new IllegalArgumentException("a region declares each data and side once, and"
                    + " leaves each a value beside what it is held to: " + bounds + " " + held);
        }
        if (!bounds.containsAll(asFarOutAsCanBe)) {
            throw new IllegalArgumentException("as far out as can be is said of a bound of the"
                    + " region: " + asFarOutAsCanBe);
        }
    }

    /**
     * The region one reading's {@code asked} declare beside {@code held}, what that reading says
     * each data they are declared on is already left, each data and side bounded by the tightest
     * of them, a value of the input shown to hold all they declare on at once, with nothing yet
     * said of how far out — or none where that leaves some data no value.
     */
    public static Optional<WhatKeepsEveryRunGoing> of(
            Collection<ABoundThatKeepsEveryRunGoing> asked,
            Map<ABoundThatKeepsEveryRunGoing.Holder, ABoundThatKeepsEveryRunGoing.Held> held) {
        Set<ABoundThatKeepsEveryRunGoing.Holder> declaredOn = new LinkedHashSet<>();
        asked.forEach(each -> declaredOn.add(each.holder()));
        return tightest(asked, held, Set.of(declaredOn));
    }

    /** The region {@code asked} declare beside {@code held}, each data and side bounded by the
     *  tightest of them, with {@code shown} — or none where that leaves some data no value. */
    private static Optional<WhatKeepsEveryRunGoing> tightest(
            Collection<ABoundThatKeepsEveryRunGoing> asked,
            Map<ABoundThatKeepsEveryRunGoing.Holder, ABoundThatKeepsEveryRunGoing.Held> held,
            Set<Set<ABoundThatKeepsEveryRunGoing.Holder>> shown) {
        Map<ABoundThatKeepsEveryRunGoing.Side, ABoundThatKeepsEveryRunGoing> tightest =
                new LinkedHashMap<>();
        for (ABoundThatKeepsEveryRunGoing each : asked) {
            tightest.merge(each.side(), each, (one, other) -> one.within(other) ? one : other);
        }
        return keepsEveryDataAValue(tightest.values(), held)
                ? Optional.of(new WhatKeepsEveryRunGoing(new LinkedHashSet<>(tightest.values()),
                        held, Set.of(), shown))
                : Optional.empty();
    }

    /** The same region, with {@code farOut}, bounds of it, said as far out as each can be. */
    public WhatKeepsEveryRunGoing asFarOutAsCanBe(Set<ABoundThatKeepsEveryRunGoing> farOut) {
        return new WhatKeepsEveryRunGoing(bounds, held, farOut, shownTogether);
    }

    /**
     * What two readings of one rule say of the region, as one: the declarations of both, each data
     * and side bounded by the tighter, so that a run within it is within each, beside what both
     * say each data is left, and every set of what is declared on either was shown to hold at once
     * — and none where either says none, a run of that reading being one no declaration said keeps
     * going, or where the two together leave some data no value. How far out a bound goes is shown
     * of one region, and stands only where the two together are that region, whatever order either
     * met its declarations in.
     *
     * <p>Nothing here asks whether a value holds them all at once ({@link #heldTogether}): that is
     * of every reading of the rule, and a reading put in later may be the one that shows it. So
     * putting readings together comes to one region whatever order they are put in.
     */
    public static Optional<WhatKeepsEveryRunGoing> together(Optional<WhatKeepsEveryRunGoing> one,
                                                            Optional<WhatKeepsEveryRunGoing> other) {
        if (one.isEmpty() || other.isEmpty()) {
            return Optional.empty();
        }
        Set<ABoundThatKeepsEveryRunGoing> both = new LinkedHashSet<>(one.get().bounds);
        both.addAll(other.get().bounds);
        Map<ABoundThatKeepsEveryRunGoing.Holder, ABoundThatKeepsEveryRunGoing.Held> held =
                new LinkedHashMap<>(one.get().held);
        other.get().held.forEach((holder, each) -> held.merge(holder, each,
                ABoundThatKeepsEveryRunGoing.Held::meet));
        Set<Set<ABoundThatKeepsEveryRunGoing.Holder>> shown =
                new LinkedHashSet<>(one.get().shownTogether);
        shown.addAll(other.get().shownTogether);
        return tightest(both, held, shown).map(region -> {
            Set<ABoundThatKeepsEveryRunGoing> standing = new LinkedHashSet<>();
            for (WhatKeepsEveryRunGoing each : List.of(one.get(), other.get())) {
                if (each.bounds.equals(region.bounds)) {
                    standing.addAll(each.asFarOutAsCanBe);
                }
            }
            return region.asFarOutAsCanBe(standing);
        });
    }

    /**
     * What two findings of one step say keeps its runs going, put together: the regions both say
     * ({@link #together}), or the one either says where the other says none. A finding of a step
     * that says no region there is one whose declarations are said at another step of what was
     * read with it, and takes nothing from what is said here.
     */
    public static Optional<WhatKeepsEveryRunGoing> besideWhatIsSaidAtOneStep(
            Optional<WhatKeepsEveryRunGoing> one, Optional<WhatKeepsEveryRunGoing> other) {
        return one.isEmpty() ? other : other.isEmpty() ? one : together(one, other);
    }

    /**
     * The region as a report says it: this, where a value of the input was shown to hold all of
     * it at once ({@link #heldTogether}), and none where not. The one place that is asked, and
     * only of the region every reading of the rule put together comes to: what is put together
     * before that may yet meet the reading that shows it.
     */
    public Optional<WhatKeepsEveryRunGoing> said() {
        return heldTogether() ? Optional.of(this) : Optional.empty();
    }

    /**
     * Whether a value of the input was shown to hold every declaration of the region at once: one
     * reading showed it of all they declare on, and the bounds the others add are of the same
     * places, each only tighter.
     */
    public boolean heldTogether() {
        Set<ABoundThatKeepsEveryRunGoing.Holder> declaredOn = new LinkedHashSet<>();
        bounds.forEach(each -> declaredOn.add(each.holder()));
        return shownTogether.stream().anyMatch(shown -> shown.containsAll(declaredOn));
    }

    /** Whether {@code bound} is as far out as a bound of this region can be. */
    public boolean asFarOutAsCanBe(ABoundThatKeepsEveryRunGoing bound) {
        return asFarOutAsCanBe.contains(bound);
    }

    /** Whether every data {@code bounds} declare on keeps a whole number under them, within what
     *  {@code held} says it is already left, every one of which is a value. */
    private static boolean keepsEveryDataAValue(
            Collection<ABoundThatKeepsEveryRunGoing> bounds,
            Map<ABoundThatKeepsEveryRunGoing.Holder, ABoundThatKeepsEveryRunGoing.Held> held) {
        Map<ABoundThatKeepsEveryRunGoing.Holder, ABoundThatKeepsEveryRunGoing.Held> left =
                new LinkedHashMap<>(held);
        for (ABoundThatKeepsEveryRunGoing each : bounds) {
            left.computeIfPresent(each.holder(), (_, was) -> was.bounded(each.at(), each.atMost()));
        }
        return left.values().stream().noneMatch(ABoundThatKeepsEveryRunGoing.Held::none);
    }
}
