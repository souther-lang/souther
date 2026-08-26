package souther.compiler.query;

import souther.compiler.partition.BorderObligationPoint;
import souther.compiler.partition.Demand;
import souther.compiler.partition.PointRole;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Everything known about one point a row is owed at: what it asks, and what all the readings of it
 * came to.
 *
 * <p>What a report prints, what a build refuses over and what an editor offers are readings of
 * these. A {@link BorderAssessment} beside one is a border as some position of some behavior met it,
 * and there is one of those per position of every behavior carrying the type. Answered from an
 * occurrence, one clause of {@code UserId} was 126 things to write a row for over {@code crm}
 * (issue #1062).
 *
 * <p><b>One of these per point and not per line.</b> A line owes as many as four things and they are
 * not one piece of work: a row at the line and a row beside it are two values, and two runs beside
 * one line that stop in different places are two rows to write. Which of them a reading owes is the
 * border's own answer ({@link souther.compiler.partition.Border#owes}), so nothing here decides it
 * again — and a line has no assessment of its own, only the points it owes. A report that shows a
 * border whole groups these by the line and joins them with the border's four answers, because a
 * role nobody is owed a row in has no point here to be found by.
 *
 * <p><b>What is owed is the same at every reading, and that is checked rather than folded.</b> A
 * {@link Demand} is what the point asks — a criterion over the levels of the quantity the line cut,
 * or a reason no row is asked for — and none of it is about where the line was read. So two readings
 * of one point that disagree about it have not disagreed: something has called two points one, and
 * the identity is what is wrong. Joined instead — the stronger demand winning, or the two merged —
 * that mistake would come out as a report asking for a row at a point some other line owns.
 */
public record BorderObligationPointAssessment(BorderObligationPoint point, String axis,
                                              Demand demand, ItemAssessment.Owed item,
                                              java.util.SequencedMap<Reading, BorderAssessment>
                                                      met) {

    /**
     * One reading of the line: which behavior met it, and at which of that behavior's positions.
     *
     * <p><b>The position and not the behavior alone.</b> One behavior can carry the type at more
     * than one position — {@code { a: Code, b: Code }} is two readings of {@code Code}'s line in
     * whichever behavior takes that record — and what a search of one of them comes to is a fact
     * about that position: the rules reaching it, and the values its decoder took. Told apart by
     * the behavior alone, the second position's answer was dropped and which one survived was
     * whichever the search walked first.
     *
     * <p>{@code at} is the bare term a row at the position is labelled with — {@code
     * String.length(x.a)} — and two readings of one line in one behavior are two positions, so it
     * tells them apart. The behavior-qualified spelling is not used here because it would say the
     * behavior twice; where the pair would not tell two readings apart, {@link #across} refuses
     * rather than keeping one of them.
     */
    public record Reading(String behavior, String at) {

        public Reading {
            if (behavior == null || at == null) {
                throw new IllegalArgumentException("a reading is some behavior's, somewhere in it");
            }
        }

        @Override
        public String toString() {
            return behavior + "/" + at;
        }
    }

    public BorderObligationPointAssessment {
        if (point == null) {
            throw new IllegalArgumentException("an assessment is of some point");
        }
        if (met == null || met.isEmpty()) {
            throw new IllegalArgumentException(
                    "a point is what its readings came to, and this is none of them: " + point);
        }
        if (demand == null || item == null) {
            throw new IllegalArgumentException(
                    "a point owed a row asks for one and came to something: " + point);
        }
        if (axis == null) {
            throw new IllegalArgumentException("a line is a line on something: " + point);
        }
        met = java.util.Collections.unmodifiableSequencedMap(new LinkedHashMap<>(met));
    }

    /**
     * The points of a module, from every reading of every one of them.
     *
     * <p>In the order the readings were made, so that what a report prints is read against the one
     * before it. What tells the points apart is what a border says it owes and nothing here: a
     * caller that grouped by anything else — the label, the rule, the position — would be deciding
     * what a debt is a second time and somewhere else.
     */
    public static List<BorderObligationPointAssessment> across(
            Map<String, List<BorderAssessment>> byBehavior,
            java.util.function.Function<BorderObligationPoint, String> named) {
        Map<BorderObligationPoint, java.util.SequencedMap<Reading, BorderAssessment>> byPoint =
                new LinkedHashMap<>();
        byBehavior.forEach((behavior, readings) -> {
            for (BorderAssessment reading : readings) {
                Reading where = new Reading(behavior, reading.border().cut().left());
                for (BorderObligationPoint owed : reading.border().owes()) {
                    BorderAssessment already = byPoint
                            .computeIfAbsent(owed, _ -> new LinkedHashMap<>()).put(where, reading);
                    if (already != null) {
                        // Two readings this cannot tell apart, which is not two readings: what a
                        // search of one of them came to would stand for the other, chosen by the
                        // order the walk took. Refused rather than kept, for the reason `owedAt`
                        // refuses one behavior's lines holding one line twice.
                        throw new IllegalStateException("one behavior reads " + owed + " twice at "
                                + where + ", so the two readings of it are one");
                    }
                }
            }
        });
        List<BorderObligationPointAssessment> out = new ArrayList<>();
        byPoint.forEach((point, met) -> out.add(of(point, named.apply(point), met)));
        return List.copyOf(out);
    }

    /**
     * One point, from the readings of it, on a quantity called {@code axis}.
     *
     * <p>What the line is on is handed in rather than taken from a reading, because that is the
     * whole of what a debt is not. A reading names the position it met the line at — {@code
     * String.length(draft.owner)} — and there are as many of those as there are positions carrying
     * the type; what the author wrote is {@code String.length(value)}, and it is read from the
     * declaration ({@link souther.compiler.check.DeclaredBorders}).
     */
    public static BorderObligationPointAssessment of(BorderObligationPoint point, String axis,
                                                     java.util.SequencedMap<Reading,
                                                             BorderAssessment> met) {
        List<BorderAssessment> readings = List.copyOf(met.values());
        Demand asked = asked(point, readings);
        return new BorderObligationPointAssessment(point, axis, asked,
                came(point.role(), readings, asked), met);
    }

    /** Every reading of the line that owes this point, in the order they were made. */
    public List<BorderAssessment> readings() {
        return List.copyOf(met.values());
    }

    /** Which line of the model a row here is owed for. */
    public souther.compiler.partition.BorderObligationId id() {
        return point.line();
    }

    /** Which of a border's four points this is. */
    public PointRole role() {
        return point.role();
    }

    /**
     * What the point asks, which every reading of it says the same way.
     *
     * <p>Checked here, because this is where two readings of one point first stand beside each
     * other. A disagreement is not something to resolve: it says the two are not one point, and the
     * identity that put them together is the defect. What it names is both readings, since which of
     * them is the wrong one is exactly what is not known.
     */
    private static Demand asked(BorderObligationPoint point, List<BorderAssessment> readings) {
        Demand asked = readings.get(0).border().demand(point.role());
        for (BorderAssessment reading : readings) {
            Demand also = reading.border().demand(point.role());
            if (!asked.sameAs(also)) {
                throw new IllegalStateException("two readings of one point disagree about what it"
                        + " asks for, so they are not one point: " + point
                        + " asks " + asked + " at " + readings.get(0).border().cut().named()
                        + " and " + also + " at " + reading.border().cut().named());
            }
        }
        return asked;
    }

    /**
     * What the readings came to.
     *
     * <p>The coverage is folded ({@link ItemAssessment.Coverage#acrossTheReadings}). So is what
     * building a value came to, and it is here for one thing: that a value at the point was built
     * is evidence the point exists, and whether a point exists is what tells a line no row stands at
     * from one no row could stand at ({@link ItemAssessment#isUnmetGap}). Every reading of one point
     * asks the same of a row — which is checked, not assumed — so a value built at one of them is a
     * value at this point.
     *
     * <p><b>Not the row a point is offered.</b> A row is offered once for a point, and which reading
     * composes it is a search over the readings rather than a fold of them ({@link
     * DeclarationResolver}): the row here is written in one behavior's terms and choosing it as the
     * one to offer would be choosing a representative, which is the mistake this whole value exists
     * to undo. What it is here for is that a value at the point was built, which is evidence the
     * point exists.
     */
    private static ItemAssessment.Owed came(PointRole role, List<BorderAssessment> readings,
                                            Demand asked) {
        if (asked instanceof Demand.NotOwed not) {
            throw new IllegalStateException(
                    "a point nobody is owed a row at, assessed as one that is: " + not.reason());
        }
        List<Measurement<ItemAssessment.Coverage>> coverage = new ArrayList<>();
        ItemAssessment.Attempt built = null;
        // Whether a value at the point exists is a fact about the point and not about the reading
        // that reached it: one reading proving it proves it. The other two states are what a reading
        // says about itself, so the weaker of them stands only where nothing proved anything.
        ItemAssessment.WritabilityProjection projection =
                ItemAssessment.WritabilityProjection.NOT_COMPUTED;
        for (BorderAssessment reading : readings) {
            ItemAssessment.Owed owed = reading.owedAt(role);
            if (owed == null) {
                throw new IllegalStateException(
                        "a reading owing nothing at a point it owes one at: " + role);
            }
            coverage.add(owed.coverage());
            if (built == null && owed.attempt() instanceof ItemAssessment.Attempt.Built) {
                built = owed.attempt();
            }
            if (owed.projection().proves()) {
                projection = ItemAssessment.WritabilityProjection.PROVEN;
            } else if (projection != ItemAssessment.WritabilityProjection.PROVEN
                    && owed.projection() == ItemAssessment.WritabilityProjection.UNPROVEN) {
                projection = ItemAssessment.WritabilityProjection.UNPROVEN;
            }
        }
        return new ItemAssessment.Owed(asked.criterion(),
                ItemAssessment.Coverage.acrossTheReadings(coverage), projection, built);
    }

    /** The measured half, which a point owed a row always has. */
    public ItemAssessment.Owed owed() {
        return item;
    }

    /**
     * Which behaviors read the line at this point, in the order the module declares them.
     *
     * <p>Not part of what the point is — a line is owed once however many behaviors carry the type —
     * and here because an editor's offer stands beside a behavior. What a row written for that
     * behavior settles is this point, so an offer there has to know the point is one of the things
     * it would answer. Without it the offer beside a behavior went quiet as soon as the only work
     * left was a line the declaration is owed (issue #1062).
     */
    public boolean carriedBy(String behavior) {
        return met.keySet().stream().anyMatch(each -> each.behavior().equals(behavior));
    }

    /** The same, as the list of them. Distinct, because a behavior reading one line at two
     *  positions carries it once. */
    public List<String> carriedBy() {
        return met.keySet().stream().map(Reading::behavior).distinct().toList();
    }

    /**
     * What this point asks of a row, as a report writes it.
     *
     * <p>The same sentence a reading's point writes ({@link BorderAssessment.Point#said}), on what
     * the declaration wrote rather than on the position a reading met it at. The two are joined by
     * a consumer against one of a border's items, so they are spelled by one rule and not two.
     */
    public String said() {
        return role().againstTheLine() ? axis + " = " + against()
                : axis + " " + operator() + " " + against();
    }

    /** How this point relates a row's value to what it is against. */
    public String operator() {
        return demand.criterion().operator();
    }

    /**
     * What a row here would have to do, as a report writes it.
     *
     * <p>Written on a reading's quantity, and any of them will do. What a criterion writes is the
     * level in the terms of the order that level is on, and which order that is, is part of what a
     * point is — the readings of one point cut one carrier at one place, which is checked where
     * their demands are. So this is not a reading standing in for the rest; it is the one answer
     * they all give.
     */
    public String against() {
        return demand.criterion().written(met.firstEntry().getValue().border().cut().of(), axis);
    }
}
