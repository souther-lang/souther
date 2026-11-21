package souther.compiler.inputs;

import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.TreeSet;

/**
 * How a statement can come out at each value of one term, each way on its own: where a row with
 * the term at that value is shown to have it hold, where none can, and where neither is shown —
 * and the same of it failing.
 *
 * <p>Two questions and not one. {@link WhatARelationLeavesUndivided.Leaves} asks them together: a
 * value settles the relation, or leaves it either way, and where some value is shown neither, the
 * term is shown nothing at all. A row on the one side of the term's value may be shown where the
 * other is not, and that is said here, so that what is shown of one way is not lost for want of
 * the other.
 *
 * <p>That is what a choice's arms need. A row takes one arm, so the statement the arms answer
 * holds at a value where some arm is shown to have it hold there, and holds at none where no arm
 * can ({@link #eitherOf}). An arm that shows one way at a value and not the other leaves that
 * value to the other arms: {@code Decimal.min(x, 0.0m) <= c} is shown false at every {@code c}
 * below nought by the arm answering nought, wherever the arm answering {@code x} is not.
 *
 * <p>Neither way's answer stands for the other. A way not shown reached is not shown never
 * reached ({@link Shown#NOT_SHOWN}), and is never read as either. What says a way is reached is a
 * row: a value the term is shown to take, with values of the others it is shown to take beside it
 * ({@link WhatARelationLeavesUndivided#eachWayItComesOut}). That a relation settles a run of
 * values, or leaves them undivided, says how a row there would come out and not that there is one.
 *
 * @param spacing   how the term's values are spaced, which says whether a run holds any
 * @param stretches runs of the values the term may hold in order, each starting where the one
 *                  before ends, together every value it may hold, each answering the same at every
 *                  value it holds. A number before the first or after the last is no value of the
 *                  term. None where it may hold none
 */
public record EachWayItComesOut(Granularity spacing, List<Stretch> stretches) {

    /** What is shown of one way the statement comes out, at every value of a stretch. */
    public enum Shown {
        /** Some row with the term at the value comes out this way. */
        REACHED,
        /** No row with the term at the value comes out this way. */
        NEVER,
        /** Neither is shown. */
        NOT_SHOWN;

        /** What several alternatives a row takes one of show together: reached where one of them
         *  is, never reached where none of them can be, and otherwise not shown. */
        static Shown eitherOf(List<Shown> each) {
            if (each.contains(REACHED)) {
                return REACHED;
            }
            return each.stream().allMatch(NEVER::equals) ? NEVER : NOT_SHOWN;
        }
    }

    /**
     * A run of the term's values and what is shown of each way at every one of them.
     *
     * @param from    the lower end, or null where the run has no least
     * @param to      the upper end, or null where it has no greatest
     * @param holding what is shown of the statement holding
     * @param failing what is shown of it failing
     */
    public record Stretch(ExactCut from, ExactCut to, Shown holding, Shown failing) {

        public Stretch {
            Objects.requireNonNull(holding, "something is shown of holding, or that nothing is");
            Objects.requireNonNull(failing, "something is shown of failing, or that nothing is");
        }

        /** Whether the two ways are shown alike here and at {@code other}. */
        boolean showsAlike(Stretch other) {
            return holding == other.holding && failing == other.failing;
        }
    }

    public EachWayItComesOut {
        Objects.requireNonNull(spacing, "a term's values are spaced somehow");
        stretches = stretches.stream().sorted(Comparator.comparing(Stretch::from,
                Comparator.nullsFirst(EachWayItComesOut::byStart))).toList();
        // Each where the one before ends, or with no value of the term between them.
        for (int i = 1; i < stretches.size(); i++) {
            ExactCut end = stretches.get(i - 1).to();
            ExactCut start = stretches.get(i).from();
            if (end == null || start == null || byStart(start, startAfter(end)) < 0
                    || (byStart(startAfter(end), start) != 0 && Lattice.occupancy(spacing,
                            startAfter(end), endBefore(start)) != Lattice.Occupancy.EMPTY)) {
                throw new IllegalArgumentException("the stretches of a term's values follow on"
                        + " from one another: " + stretches);
            }
        }
    }

    /**
     * What the statement several alternatives answer shows of each way, a row taking one of them:
     * at each value, a way is reached where some alternative reaches it and never reached where
     * none can. A value some alternative may hold is one of the term's, and an alternative that
     * holds no value there has no row there, so reaches neither way.
     *
     * <p>Null where the alternatives are spaced differently, or where whether a run between their
     * ends holds a value is not worked out.
     */
    public static EachWayItComesOut eitherOf(List<EachWayItComesOut> alternatives) {
        if (alternatives.isEmpty()) {
            throw new IllegalArgumentException("a choice has some alternative");
        }
        Granularity spacing = alternatives.getFirst().spacing();
        if (alternatives.stream().anyMatch(each -> each.spacing() != spacing)) {
            return null;
        }
        // Every place a stretch of some alternative starts or stops, as the start of what lies
        // above it: between two in a row, every alternative answers one way throughout.
        TreeSet<ExactCut> starts = new TreeSet<>(EachWayItComesOut::byStart);
        boolean noLeast = false;
        boolean noGreatest = false;
        for (EachWayItComesOut each : alternatives) {
            for (Stretch stretch : each.stretches()) {
                if (stretch.from() != null) {
                    starts.add(stretch.from());
                } else {
                    noLeast = true;
                }
                if (stretch.to() != null) {
                    starts.add(startAfter(stretch.to()));
                } else {
                    noGreatest = true;
                }
            }
        }
        if (starts.isEmpty() && !noLeast) {
            return new EachWayItComesOut(spacing, List.of());
        }
        // The values from the least any alternative may hold to the greatest: a number of no
        // alternative between them is one of the term's that no row holds.
        List<ExactCut> inOrder = new ArrayList<>(starts);
        int first = noLeast ? 0 : 1;
        int last = noGreatest ? inOrder.size() : inOrder.size() - 1;
        List<Stretch> out = new ArrayList<>();
        for (int i = first; i <= last; i++) {
            ExactCut from = i == 0 ? null : inOrder.get(i - 1);
            ExactCut to = i == inOrder.size() ? null : endBefore(inOrder.get(i));
            switch (Lattice.occupancy(spacing, from, to)) {
                case UNKNOWN -> {
                    return null;
                }
                case EMPTY -> {
                    // Nothing between: the stretch below and the one above follow on at once.
                    if (!out.isEmpty()) {
                        Stretch below = out.removeLast();
                        out.add(new Stretch(below.from(), to, below.holding(), below.failing()));
                    }
                    continue;
                }
                case HOLDS -> { }
            }
            List<Shown> holding = new ArrayList<>();
            List<Shown> failing = new ArrayList<>();
            for (EachWayItComesOut each : alternatives) {
                Stretch at = each.stretchStartingAt(from);
                holding.add(at == null ? Shown.NEVER : at.holding());
                failing.add(at == null ? Shown.NEVER : at.failing());
            }
            Stretch here = new Stretch(from, to, Shown.eitherOf(holding), Shown.eitherOf(failing));
            if (!out.isEmpty() && out.getLast().showsAlike(here)) {
                here = new Stretch(out.removeLast().from(), to, here.holding(), here.failing());
            }
            out.add(here);
        }
        return new EachWayItComesOut(spacing, out);
    }

    /**
     * What this leaves the term as a relation's reading says it ({@link
     * WhatARelationLeavesUndivided.Leaves}): divided by nothing where both ways are reached at
     * every value some row may hold, or where the statement comes out one way at all of them;
     * the runs at which one way is never reached settling it the other, every other value
     * reached both ways — or null where some value may come out either way and is not shown
     * reached both, or a value no row holds lies between values some row may hold.
     *
     * @param ofTheTypeAlone lines the readings this was made of said the orders' ends alone draw
     * @param ofTheModel     lines they said the model draws
     */
    public WhatARelationLeavesUndivided.Leaves leaves(
            Set<WhatARelationLeavesUndivided.Line> ofTheTypeAlone,
            Set<WhatARelationLeavesUndivided.Line> ofTheModel) {
        List<Stretch> held = new ArrayList<>(stretches);
        while (!held.isEmpty() && noRow(held.getFirst())) {
            held.removeFirst();
        }
        while (!held.isEmpty() && noRow(held.getLast())) {
            held.removeLast();
        }
        if (held.isEmpty()) {
            return null;
        }
        boolean whole = spacing == Granularity.DISCRETE;
        List<WhatARelationLeavesUndivided.SettledRun> runs = new ArrayList<>();
        boolean bothSomewhere = false;
        for (Stretch each : held) {
            if (noRow(each)) {
                return null;
            }
            boolean mayHold = each.holding() != Shown.NEVER;
            boolean mayFail = each.failing() != Shown.NEVER;
            if (mayHold && mayFail) {
                if (each.holding() != Shown.REACHED || each.failing() != Shown.REACHED) {
                    return null;
                }
                bothSomewhere = true;
            } else {
                runs.add(new WhatARelationLeavesUndivided.SettledRun(lower(each.from(), whole),
                        upper(each.to(), whole), mayHold));
            }
        }
        if (runs.isEmpty() || (!bothSomewhere && runs.size() == 1)) {
            return new WhatARelationLeavesUndivided.Leaves.Undivided();
        }
        WhatARelationLeavesUndivided.Leaves.Settled settled =
                new WhatARelationLeavesUndivided.Leaves.Settled(runs,
                        lower(held.getFirst().from(), whole), upper(held.getLast().to(), whole),
                        whole, List.of(), List.of());
        return new WhatARelationLeavesUndivided.Leaves.Settled(runs, settled.least(),
                settled.greatest(), whole, settled.lines().stream()
                        .filter(line -> ofTheTypeAlone.contains(line)
                                && !ofTheModel.contains(line)).toList(), List.of());
    }

    private static boolean noRow(Stretch stretch) {
        return stretch.holding() == Shown.NEVER && stretch.failing() == Shown.NEVER;
    }

    /** {@code start} as the least value a run of whole numbers holds where it is one, so that
     *  the lines drawn of it name the number they are at. */
    private static ExactCut lower(ExactCut start, boolean whole) {
        if (start == null || !whole || start.inclusive()) {
            return start;
        }
        BigInteger least = start.at().floor().map(each -> each.add(BigInteger.ONE)).orNull();
        return least == null ? start : ExactCut.inclusive(ExactRatio.of(least));
    }

    /** {@code end} as the greatest value a run of whole numbers holds, as {@link #lower}. */
    private static ExactCut upper(ExactCut end, boolean whole) {
        if (end == null || !whole || end.inclusive()) {
            return end;
        }
        BigInteger most = end.at().ceiling().map(each -> each.subtract(BigInteger.ONE)).orNull();
        return most == null ? end : ExactCut.inclusive(ExactRatio.of(most));
    }

    /** The stretch holding every value from {@code from} up to the next place one starts or
     *  stops, or null where none does: one of {@link #eitherOf}'s runs, which no stretch here
     *  starts or stops inside. */
    private Stretch stretchStartingAt(ExactCut from) {
        for (Stretch each : stretches) {
            boolean startsBelow = each.from() == null
                    || (from != null && byStart(each.from(), from) <= 0);
            boolean stopsAbove = each.to() == null || from == null
                    || byStart(from, startAfter(each.to())) < 0;
            if (startsBelow && stopsAbove) {
                return each;
            }
        }
        return null;
    }

    /** What is shown of the statement failing where the term is at {@code value}: not shown where
     *  that is no value of the term. */
    public Shown failingAt(ExactRatio value) {
        for (Stretch each : stretches) {
            boolean fromBelow = each.from() == null || each.from().at().compareTo(value) < 0
                    || (each.from().inclusive() && each.from().at().compareTo(value) == 0);
            boolean toAbove = each.to() == null || each.to().at().compareTo(value) > 0
                    || (each.to().inclusive() && each.to().at().compareTo(value) == 0);
            if (fromBelow && toAbove) {
                return each.failing();
            }
        }
        return Shown.NOT_SHOWN;
    }

    /** Whether the term may hold some value, and neither way is left unshown at any of them. */
    public boolean showsEveryValue() {
        return !stretches.isEmpty() && stretches.stream().allMatch(each ->
                each.holding() != Shown.NOT_SHOWN && each.failing() != Shown.NOT_SHOWN);
    }

    /** Whether a row is shown for each way at every number: the stretches have no least and no
     *  greatest, and both ways are reached at each. */
    public boolean reachesEveryNumberBothWays() {
        return !stretches.isEmpty() && stretches.getFirst().from() == null
                && stretches.getLast().to() == null && stretches.stream().allMatch(each ->
                        each.holding() == Shown.REACHED && each.failing() == Shown.REACHED);
    }

    /**
     * Where what is shown changes, each as the start of the values above it: the start of each
     * stretch that shows the two ways otherwise than the one below it, which it follows on from.
     */
    public List<ExactCut> whereItTurns() {
        List<ExactCut> out = new ArrayList<>();
        for (int i = 1; i < stretches.size(); i++) {
            if (!stretches.get(i).showsAlike(stretches.get(i - 1))) {
                out.add(stretches.get(i).from());
            }
        }
        return out;
    }

    /**
     * How two starts of runs stand: the one below first, and of two at one number, the one taking
     * the number in, since the run it starts holds more.
     */
    static int byStart(ExactCut one, ExactCut other) {
        int order = one.at().compareTo(other.at());
        if (order != 0) {
            return order;
        }
        return Boolean.compare(!one.inclusive(), !other.inclusive());
    }

    /** The start of the values above a run ending at {@code end}. */
    static ExactCut startAfter(ExactCut end) {
        return new ExactCut(end.at(), !end.inclusive());
    }

    /** The end of the values below a run starting at {@code start}. */
    static ExactCut endBefore(ExactCut start) {
        return new ExactCut(start.at(), !start.inclusive());
    }
}
