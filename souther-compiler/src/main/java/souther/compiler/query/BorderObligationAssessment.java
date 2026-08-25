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
 * <p><b>Total over {@link PointRole}, the way an occurrence is.</b> A line answers for every role
 * and so does this, so a reader asking what one of them came to is never answered by an entry that
 * is not there.
 *
 * <p><b>What is owed is the same at every reading, and that is checked rather than folded.</b> A
 * {@link Demand} is what the line asks — a criterion over the levels of the quantity it cut, or a
 * reason no row is asked for — and none of it is about where the line was read. So two readings of
 * one debt that disagree about it have not disagreed: something has called two authored lines one,
 * and the identity is what is wrong. Joined instead — the stronger demand winning, or the two
 * merged — that mistake would come out as a report asking for a row at a point some other line
 * owns.
 */
public record BorderObligationAssessment(BorderObligationId id, Map<PointRole, Demand> demands,
                                         Map<PointRole, ItemAssessment> items,
                                         List<BorderAssessment> readings) {

    public BorderObligationAssessment {
        if (id == null) {
            throw new IllegalArgumentException("a debt is some authored line's");
        }
        if (readings == null || readings.isEmpty()) {
            throw new IllegalArgumentException(
                    "a debt is what its readings came to, and this is none of them: " + id);
        }
        if (demands == null || !demands.keySet().equals(EnumSet.allOf(PointRole.class))
                || items == null || !items.keySet().equals(EnumSet.allOf(PointRole.class))) {
            throw new IllegalArgumentException(
                    "a debt answering for some of its point roles and not others: " + id);
        }
        readings = List.copyOf(readings);
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
    public static List<BorderObligationAssessment> across(List<BorderAssessment> readings) {
        Map<BorderObligationId, List<BorderAssessment>> byDebt = new LinkedHashMap<>();
        for (BorderAssessment reading : readings) {
            byDebt.computeIfAbsent(reading.border().obligation(), _ -> new ArrayList<>())
                    .add(reading);
        }
        List<BorderObligationAssessment> out = new ArrayList<>();
        byDebt.forEach((id, of) -> out.add(of(id, of)));
        return List.copyOf(out);
    }

    /** One debt, from the readings of it. */
    public static BorderObligationAssessment of(BorderObligationId id,
                                                List<BorderAssessment> readings) {
        Map<PointRole, Demand> demands = new EnumMap<>(PointRole.class);
        Map<PointRole, ItemAssessment> items = new EnumMap<>(PointRole.class);
        for (PointRole role : EnumSet.allOf(PointRole.class)) {
            demands.put(role, asked(id, role, readings));
            items.put(role, at(role, readings, demands.get(role)));
        }
        return new BorderObligationAssessment(id, demands, items, readings);
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
     * <p>The coverage is folded ({@link ItemAssessment.Coverage#acrossTheReadings}); what building a
     * value came to is not here at all. A row offered for a point is offered once for the debt and
     * not once per reading, and choosing which reading composes it is a search rather than a fold —
     * so it stays where the readings are until there is something to say about it.
     */
    private static ItemAssessment at(PointRole role, List<BorderAssessment> readings, Demand asked) {
        if (asked instanceof Demand.NotOwed not) {
            return new ItemAssessment.NotOwed(not.reason());
        }
        List<Measurement<ItemAssessment.Coverage>> coverage = new ArrayList<>();
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
            if (owed.projection().proves()) {
                projection = ItemAssessment.WritabilityProjection.PROVEN;
            } else if (projection != ItemAssessment.WritabilityProjection.PROVEN
                    && owed.projection() == ItemAssessment.WritabilityProjection.UNPROVEN) {
                projection = ItemAssessment.WritabilityProjection.UNPROVEN;
            }
        }
        return new ItemAssessment.Owed(asked.criterion(),
                ItemAssessment.Coverage.acrossTheReadings(coverage), projection, null);
    }

    /** What became of one role. Never null. */
    public ItemAssessment at(PointRole role) {
        return items.get(role);
    }

    /** The measured half of one role, or null where no row is owed there. */
    public ItemAssessment.Owed owedAt(PointRole role) {
        return at(role) instanceof ItemAssessment.Owed owed ? owed : null;
    }

    /** The rule that drew the line, as the readings met it. */
    public souther.compiler.partition.OriginRef origin() {
        return id.origin();
    }
}
