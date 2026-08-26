package souther.compiler.query;

import souther.compiler.partition.BorderObligationId;
import souther.compiler.partition.Demand;
import souther.compiler.partition.PointRole;

import java.util.ArrayList;
import java.util.EnumMap;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Everything known about one authored line: what it asks at each of its four points, and what all
 * the readings of it came to.
 *
 * <p>What a report prints, what a build refuses over and what an editor offers are readings of this.
 * A {@link BorderAssessment} beside it is one <em>occurrence</em> — the line as some position of
 * some behavior met it — and there is one of those per position of every behavior carrying the type.
 * Answered from an occurrence, one clause of {@code UserId} was 126 things to write a row for over
 * {@code crm} (issue #1062).
 *
 * <p><b>The two points against the line, and not the four an occurrence answers for.</b> {@code ON}
 * and {@code OFF} are values of the quantity the rule cut: whether a row standing at length 1 is
 * believed is a question about {@code UserId} and the same question wherever the type is carried.
 * {@code IN} and {@code OUT} are not values but the two <em>regions</em> either side of the line,
 * and where a region stops is settled by every other rule reaching that position — {@code Cm}'s
 * lower end at 0 runs to 150 at a {@code parcel.length} the record caps and runs on at an
 * {@code order.straw} nothing else bounds. A row well inside one is not a row that could stand at
 * the other at all, so evidence there is not interchangeable and the point is owed per reading, as
 * it was.
 *
 * <p>Which is the split {@link PointRole#againstTheLine} already names, and the one the two halves
 * of this technique were counted under before they were brought together: the regions were the
 * measure that counts the classes a position is divided into, and a class of a position is the
 * position's.
 *
 * <p>Total over the roles it does answer for, so a reader asking what one of them came to is never
 * answered by an entry that is not there.
 *
 * <p><b>What is owed is the same at every reading, and that is checked rather than folded.</b> A
 * {@link Demand} is what the line asks — a criterion over the levels of the quantity it cut, or a
 * reason no row is asked for — and none of it is about where the line was read. So two readings of
 * one debt that disagree about it have not disagreed: something has called two authored lines one,
 * and the identity is what is wrong. Joined instead — the stronger demand winning, or the two
 * merged — that mistake would come out as a report asking for a row at a point some other line
 * owns.
 */
public record BorderObligationAssessment(BorderObligationId id, String axis,
                                         Map<PointRole, Demand> demands,
                                         Map<PointRole, ItemAssessment> items,
                                         java.util.SequencedMap<Reading, BorderAssessment> met) {

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

    /**
     * The roles a debt answers for: the two the line names a value at.
     *
     * <p>The other two are regions of a position rather than values of the line, so they are owed
     * per reading and are not here ({@link PointRole#againstTheLine}).
     */
    public static final java.util.Set<PointRole> AGAINST_THE_LINE =
            java.util.Collections.unmodifiableSet(EnumSet.of(PointRole.ON, PointRole.OFF));

    public BorderObligationAssessment {
        if (id == null) {
            throw new IllegalArgumentException("a debt is some authored line's");
        }
        if (met == null || met.isEmpty()) {
            throw new IllegalArgumentException(
                    "a debt is what its readings came to, and this is none of them: " + id);
        }
        if (demands == null || !demands.keySet().equals(AGAINST_THE_LINE)
                || items == null || !items.keySet().equals(AGAINST_THE_LINE)) {
            throw new IllegalArgumentException(
                    "a debt answering for some of the points against its line and not others: "
                            + id + " " + (demands == null ? null : demands.keySet()));
        }
        if (axis == null) {
            throw new IllegalArgumentException("a line is a line on something: " + id);
        }
        met = java.util.Collections.unmodifiableSequencedMap(new LinkedHashMap<>(met));
        demands = java.util.Collections.unmodifiableMap(new EnumMap<>(demands));
        items = java.util.Collections.unmodifiableMap(new EnumMap<>(items));
    }

    /**
     * The debts of a module, from every reading of every one of them.
     *
     * <p>In the order the readings were made, so that what a report prints is read against the one
     * before it. What tells the readings apart is what {@link BorderObligationId} answers and
     * nothing here: a caller that grouped by anything else — the label, the rule, the position —
     * would be deciding what a debt is a second time and somewhere else.
     */
    public static List<BorderObligationAssessment> across(
            Map<String, List<BorderAssessment>> byBehavior,
            java.util.function.Function<BorderObligationId, String> named) {
        Map<BorderObligationId, java.util.SequencedMap<Reading, BorderAssessment>> byDebt =
                new LinkedHashMap<>();
        byBehavior.forEach((behavior, readings) -> {
            for (BorderAssessment reading : readings) {
                BorderObligationId id = reading.border().obligation();
                Reading where = new Reading(behavior, reading.border().cut().left());
                BorderAssessment already = byDebt
                        .computeIfAbsent(id, _ -> new LinkedHashMap<>()).put(where, reading);
                if (already != null) {
                    // Two readings this cannot tell apart, which is not two readings: what a search
                    // of one of them came to would stand for the other, chosen by the order the
                    // walk took. Refused rather than kept, for the reason `owedAt` refuses one
                    // behavior's lines holding one line twice.
                    throw new IllegalStateException("one behavior reads " + id + " twice at "
                            + where + ", so the two readings of it are one");
                }
            }
        });
        List<BorderObligationAssessment> out = new ArrayList<>();
        byDebt.forEach((id, met) -> out.add(of(id, named.apply(id), met)));
        return List.copyOf(out);
    }

    /**
     * One debt, from the readings of it, called {@code axis}.
     *
     * <p>What the line is on is handed in rather than taken from a reading, because that is the
     * whole of what a debt is not. A reading names the position it met the line at — {@code
     * String.length(draft.owner)} — and there are as many of those as there are positions carrying
     * the type; what the author wrote is {@code String.length(value)}, and it is read from the
     * declaration ({@link souther.compiler.check.DeclaredBorders}).
     */
    public static BorderObligationAssessment of(BorderObligationId id, String axis,
                                                java.util.SequencedMap<Reading, BorderAssessment>
                                                        met) {
        List<BorderAssessment> readings = List.copyOf(met.values());
        Map<PointRole, Demand> demands = new EnumMap<>(PointRole.class);
        Map<PointRole, ItemAssessment> items = new EnumMap<>(PointRole.class);
        for (PointRole role : AGAINST_THE_LINE) {
            demands.put(role, asked(id, role, readings));
            items.put(role, at(role, readings, demands.get(role)));
        }
        return new BorderObligationAssessment(id, axis, demands, items, met);
    }

    /** Every reading of the line, in the order they were made. */
    public List<BorderAssessment> readings() {
        return List.copyOf(met.values());
    }

    /**
     * What the line asks in one role, which every reading of it says the same way.
     *
     * <p>Checked here, because this is where two readings of one debt first stand beside each other.
     * A disagreement is not something to resolve: it says the two are not one line, and the identity
     * that put them together is the defect. What it names is both readings, since which of them is
     * the wrong one is exactly what is not known.
     */
    private static Demand asked(BorderObligationId id, PointRole role,
                                List<BorderAssessment> readings) {
        Demand asked = readings.get(0).border().demand(role);
        for (BorderAssessment reading : readings) {
            Demand also = reading.border().demand(role);
            if (!asked.equals(also)) {
                throw new IllegalStateException("two readings of one line disagree about what its "
                        + role + " point asks for, so they are not one line: " + id
                        + " asks " + asked + " at " + readings.get(0).border().cut().named()
                        + " and " + also + " at " + reading.border().cut().named());
            }
        }
        return asked;
    }

    /**
     * What the readings came to in one role.
     *
     * <p>The coverage is folded ({@link ItemAssessment.Coverage#acrossTheReadings}). So is what
     * building a value came to, and it is here for one thing: that a value at the point was built
     * is evidence the point exists, and whether a point exists is what tells a line no row stands at
     * from one no row could stand at ({@link ItemAssessment#isUnmetGap}). The two points a debt
     * answers for ask the same of a row at every reading — which is checked, not assumed — so a
     * value built at one of them is a value at this point.
     *
     * <p><b>Not the row a debt is offered.</b> A row is offered once for a line, and which reading
     * composes it is a search over the readings rather than a fold of them ({@link
     * DeclarationResolver}): the row here is written in one behavior's terms and choosing it as the
     * one to offer would be choosing a representative, which is the mistake this whole value exists
     * to undo. What it is here for is that a value at the point was built, which is evidence the
     * point exists.
     */
    private static ItemAssessment at(PointRole role, List<BorderAssessment> readings, Demand asked) {
        if (asked instanceof Demand.NotOwed not) {
            return new ItemAssessment.NotOwed(not.reason());
        }
        List<Measurement<ItemAssessment.Coverage>> coverage = new ArrayList<>();
        ItemAssessment.Attempt built = null;
        // Whether a value at the point exists is a fact about the line and not about the reading
        // that reached it: one reading proving it proves it. The other two states are what a reading
        // says about itself, so the weaker of them stands only where nothing proved anything.
        ItemAssessment.WritabilityProjection projection =
                ItemAssessment.WritabilityProjection.NOT_COMPUTED;
        for (BorderAssessment reading : readings) {
            ItemAssessment.Owed owed = reading.owedAt(role);
            if (owed == null) {
                throw new IllegalStateException(
                        "a reading owing nothing at a point its line owes one at: " + role);
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

    /**
     * What became of one of the points against the line. Never null.
     *
     * <p>Refused for a region, which is not something a debt answers for: where a region stops is
     * settled by every other rule reaching a position, so a debt has no answer to give and a null
     * would be read as one. A reader wanting a region asks the reading it is a region of.
     */
    public ItemAssessment at(PointRole role) {
        if (!AGAINST_THE_LINE.contains(role)) {
            throw new IllegalArgumentException("a debt answers for the points against its line, and "
                    + role + " is a region of a position: " + id);
        }
        return items.get(role);
    }

    /** The measured half of one of those, or null where no row is owed there. */
    public ItemAssessment.Owed owedAt(PointRole role) {
        return at(role) instanceof ItemAssessment.Owed owed ? owed : null;
    }

    /**
     * Which behaviors read this line, in the order the module declares them.
     *
     * <p>Not part of what the debt is — a line is owed once however many behaviors carry the type —
     * and here because an editor's offer stands beside a behavior. What a row written for that
     * behavior settles is this debt, so an offer there has to know the debt is one of the things it
     * would answer. Without it the offer beside a behavior went quiet as soon as the only work left
     * was a line the declaration is owed (issue #1062).
     */
    public boolean carriedBy(String behavior) {
        return met.keySet().stream().anyMatch(each -> each.behavior().equals(behavior));
    }

    /** The same, as the list of them. Distinct, because a behavior reading one line at two
     *  positions carries it once. */
    public List<String> carriedBy() {
        return met.keySet().stream().map(Reading::behavior).distinct().toList();
    }

    /** The rule that drew the line, as the readings met it. */
    public souther.compiler.partition.OriginRef origin() {
        return id.origin();
    }

    /**
     * What one point of the line asks of a row, as a report writes it.
     *
     * <p>The same sentence a reading's point writes ({@link BorderAssessment.Point#said}), on what
     * the declaration wrote rather than on the position a reading met it at. The two are joined by
     * a consumer against one of a border's items, so they are spelled by one rule and not two.
     */
    public String said(PointRole role) {
        return role.againstTheLine() ? axis + " = " + against(role)
                : axis + " " + operator(role) + " " + against(role);
    }

    /** How one point relates a row's value to what it is against, or null where none is owed. */
    public String operator(PointRole role) {
        souther.compiler.partition.Criterion criterion = demands.get(role).criterion();
        return criterion == null ? null : criterion.operator();
    }

    /**
     * What a row at one point of it would have to do, as a report writes it, or null where no row
     * is owed there.
     *
     * <p>Written on a reading's quantity, and any of them will do. What a criterion writes is the
     * level in the terms of the order that level is on, and which order that is, is part of what a
     * debt is — the readings of one debt cut one carrier at one place, which is checked where their
     * demands are. So this is not a reading standing in for the rest; it is the one answer they all
     * give.
     */
    public String against(PointRole role) {
        souther.compiler.partition.Criterion criterion = demands.get(role).criterion();
        return criterion == null ? null
                : criterion.written(met.firstEntry().getValue().border().cut().of());
    }
}
