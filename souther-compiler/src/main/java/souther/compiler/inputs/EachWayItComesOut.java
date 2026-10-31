package souther.compiler.inputs;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactCut;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Objects;
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
 * reached ({@link Shown#NOT_SHOWN}), and is never read as either.
 *
 * @param spacing   how the term's values are spaced, which says whether a stretch holds any
 * @param stretches runs of the term's values in order, apart, each answering the same at every
 *                  value it holds. A number in none is no value of the term
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
    }

    /**
     * A term parted by one line, at the values of {@code over}: the values from {@code start} up
     * hold the statement where {@code holdsAbove}, and the values below fail it, or the other way
     * round. Each side reaches its own way: a line is drawn where rows stand on both sides of it.
     *
     * @param over what holds the values the term is asked at, whose least and greatest ends are
     *             the term's ({@link #least}, {@link #greatest})
     */
    public static EachWayItComesOut parted(ExactCut start, boolean holdsAbove,
                                           EachWayItComesOut over) {
        if (over.stretches().isEmpty()) {
            return over;
        }
        Shown above = holdsAbove ? Shown.REACHED : Shown.NEVER;
        Shown below = holdsAbove ? Shown.NEVER : Shown.REACHED;
        return new EachWayItComesOut(over.spacing(), List.of(
                new Stretch(null, endBefore(start), below, above),
                new Stretch(start, null, above, below))).within(over.least(), over.greatest());
    }

    /** The lower end of the values a stretch holds, or null where they have no least. */
    public ExactCut least() {
        return stretches.isEmpty() ? null : stretches.getFirst().from();
    }

    /** The upper end of the values a stretch holds, or null where they have no greatest. */
    public ExactCut greatest() {
        return stretches.isEmpty() ? null : stretches.getLast().to();
    }

    /** This, at the values of {@code held} alone; the same where {@code held} is null. Null
     *  where an end of {@code held} is no number. */
    EachWayItComesOut within(NumericDomain.Bounds held) {
        if (held == null) {
            return this;
        }
        ExactCut least = cutOf(held.min());
        ExactCut greatest = cutOf(held.max());
        if ((held.min() != null && least == null) || (held.max() != null && greatest == null)) {
            return null;
        }
        return within(least, greatest);
    }

    /** This, at the values from {@code least} to {@code greatest} alone, each null where there
     *  is no end on that side. */
    private EachWayItComesOut within(ExactCut least, ExactCut greatest) {
        List<Stretch> out = new ArrayList<>();
        for (Stretch each : stretches) {
            ExactCut from = ExactCut.tighterLower(each.from(), least);
            ExactCut to = ExactCut.tighterUpper(each.to(), greatest);
            if (holdsAValue(spacing, from, to) == Boolean.FALSE) {
                continue;
            }
            out.add(new Stretch(from, to, each.holding(), each.failing()));
        }
        return new EachWayItComesOut(spacing, out);
    }

    /** This, without the stretches shown to hold no value of the term. */
    EachWayItComesOut withoutRunsOfNoValue() {
        return new EachWayItComesOut(spacing, stretches.stream()
                .filter(each -> holdsAValue(spacing, each.from(), each.to()) != Boolean.FALSE)
                .toList());
    }

    private static ExactCut cutOf(Endpoint end) {
        return end != null && end.at() instanceof Count count
                ? new ExactCut(count.exactly(), end.inclusive()) : null;
    }

    /**
     * What the statement several alternatives answer shows of each way, a row taking one of them:
     * at each value, a way is reached where some alternative reaches it and never reached where
     * none can, and a value is one of the term's where it is one of some alternative's. An
     * alternative that holds no value somewhere reaches nothing there.
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
        for (EachWayItComesOut each : alternatives) {
            for (Stretch stretch : each.stretches()) {
                if (stretch.from() != null) {
                    starts.add(stretch.from());
                }
                if (stretch.to() != null) {
                    starts.add(startAfter(stretch.to()));
                }
            }
        }
        List<ExactCut> inOrder = new ArrayList<>(starts);
        List<Stretch> out = new ArrayList<>();
        // Whether the stretch before is the run just below, nothing of the term lying between.
        boolean besideTheLast = false;
        for (int i = 0; i <= inOrder.size(); i++) {
            ExactCut from = i == 0 ? null : inOrder.get(i - 1);
            ExactCut to = i == inOrder.size() ? null : endBefore(inOrder.get(i));
            Boolean holds = holdsAValue(spacing, from, to);
            if (holds == null) {
                return null;
            }
            if (!holds) {
                continue;
            }
            List<Shown> holding = new ArrayList<>();
            List<Shown> failing = new ArrayList<>();
            boolean ofTheTerm = false;
            for (EachWayItComesOut each : alternatives) {
                Stretch at = each.stretchStartingAt(from);
                ofTheTerm |= at != null;
                holding.add(at == null ? Shown.NEVER : at.holding());
                failing.add(at == null ? Shown.NEVER : at.failing());
            }
            if (!ofTheTerm) {
                besideTheLast = false;
                continue;
            }
            Stretch here = new Stretch(from, to, Shown.eitherOf(holding), Shown.eitherOf(failing));
            if (besideTheLast && out.getLast().showsAlike(here)) {
                Stretch last = out.removeLast();
                here = new Stretch(last.from(), to, here.holding(), here.failing());
            }
            out.add(here);
            besideTheLast = true;
        }
        return new EachWayItComesOut(spacing, out);
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

    /** Whether neither way is left unshown at any value of the term. */
    public boolean showsEveryValue() {
        return stretches.stream().allMatch(each -> each.holding() != Shown.NOT_SHOWN
                && each.failing() != Shown.NOT_SHOWN);
    }

    /**
     * Where what is shown changes, each as the start of the values above it: the start of each
     * stretch that shows the two ways otherwise than the one below it.
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

    /**
     * Whether a run from {@code from} to {@code to} holds a value spaced {@code spacing}, or null
     * where that is not worked out. A run open on a side holds one.
     */
    private static Boolean holdsAValue(Granularity spacing, ExactCut from, ExactCut to) {
        if (from == null || to == null) {
            return true;
        }
        int order = from.at().compareTo(to.at());
        if (order > 0) {
            return false;
        }
        if (order == 0) {
            return from.inclusive() && to.inclusive() && Lattice.holds(spacing, from.at());
        }
        Lattice.Point least = Lattice.least(spacing, from);
        Lattice.Point greatest = Lattice.greatest(spacing, to);
        if (least == null || greatest == null) {
            return null;
        }
        Integer placed = Lattice.compare(least, greatest);
        return placed == null ? null : placed <= 0;
    }
}
