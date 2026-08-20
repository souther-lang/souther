package souther.compiler.query;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.partition.Border;
import souther.compiler.partition.Demand;
import souther.compiler.partition.BoundaryTarget;
import souther.compiler.partition.OriginRef;
import souther.compiler.partition.PointRole;
import souther.compiler.source.SourceId;

import java.util.EnumMap;
import java.util.EnumSet;
import java.util.Map;

/**
 * Everything known about one border: the line, and what became of each of its four coverage items.
 *
 * <p>One of these per border, made in one place. What a report prints, what a build is warned about
 * and what the generator offers are three readings of this and not three measurements.
 *
 * <p><b>Total over {@link PointRole}, the way the border it is about is.</b> A border answers for
 * every role and so does this, so a reader asking what one of them came to is never answered by an
 * entry that is not there. The measure used to be one record per obligation in a flat list, and two
 * of the four roles had no obligation to be in it — they were counted by the measure that counts a
 * position's classes, which is a different unit and has no word for a row on the far side of a line.
 */
public record BorderAssessment(Border border, Map<PointRole, ItemAssessment> items) {

    public BorderAssessment {
        if (items == null || !items.keySet().equals(EnumSet.allOf(PointRole.class))) {
            throw new IllegalArgumentException(
                    "a border assessed in some of its roles and not others: " + items);
        }
        // And each of them assessed as what the border says it owes. The two records answer the same
        // question about the same role — what is owed there — and holding them apart without holding
        // them together leaves a point the rules refuse carrying a row that is at it. What a report
        // prints and what a build refuses over read one of the two, so they may not disagree.
        for (PointRole role : EnumSet.allOf(PointRole.class)) {
            agrees(border, role, items.get(role));
        }
        items = java.util.Collections.unmodifiableMap(new EnumMap<>(items));
    }

    /**
     * That an item answers for the demand its border makes in that role.
     *
     * <p>Checked rather than derived, because the two are made by different things: the border says
     * what is owed and the measure says what became of it, and a measure that answered about a role
     * it had not been told about is the two coming apart. Deriving the item from the demand instead
     * would put the measure's answer where its question is.
     */
    private static void agrees(Border border, PointRole role, ItemAssessment item) {
        Demand demand = border.demand(role);
        switch (item) {
            case null -> throw new IllegalArgumentException(
                    "a border with a point role it names and does not assess: " + role);
            case ItemAssessment.NotOwed not -> {
                if (!(demand instanceof Demand.NotOwed owed) || owed.reason() != not.reason()) {
                    throw new IllegalArgumentException("the " + role + " point of " + border.label()
                            + " is assessed as not owed for " + not.reason()
                            + ", and its border says " + demand);
                }
            }
            case ItemAssessment.Owed owed -> {
                if (!(demand instanceof Demand.Owed asked)
                        || !asked.criterion().equals(owed.criterion())) {
                    throw new IllegalArgumentException("the " + role + " point of " + border.label()
                            + " is assessed against " + owed.criterion()
                            + ", and its border asks " + demand);
                }
            }
        }
    }

    /** What became of one role. Never null. */
    public ItemAssessment at(PointRole role) {
        return items.get(role);
    }

    /**
     * The measured half of one role, or null where no row is owed there.
     *
     * <p>For a reader that has already established which role it is asking about. Null here is a
     * reading and not a state anything can be built in: what is owed is settled where the border is
     * made, and nothing can produce an item that is both refused by the rules and sat on by a row.
     */
    public ItemAssessment.Owed owedAt(PointRole role) {
        return at(role) instanceof ItemAssessment.Owed owed ? owed : null;
    }

    /**
     * The position this border is on, as a report names it.
     *
     * <p>Asked of the shape of the line rather than of a field every shape was assumed to have. A line
     * between two positions is on neither of them, and answering with one of the two would name a
     * border after half of itself.
     */
    public String axis() {
        return border.cut().named();
    }

    /** Which shape this line has, which is what says how to read what each item asks for. */
    public BoundaryTarget.Shape shape() {
        return border.cut().shape();
    }

    /** The rule that drew the line, as a report about {@code sectionSource} writes it. */
    public String origin(SourceNameResolver names, SourceId sectionSource) {
        return border.origin().describe(names, sectionSource);
    }

    /** The rule itself, for a reader that renders it rather than printing what this would. */
    public OriginRef rule() {
        return border.origin();
    }

    /** Where the line is, as a report names it. */
    public String label() {
        return border.label();
    }

    /** What a row at one point of it would be written as, or null where none is owed there. */
    public String label(PointRole role) {
        return border.label(role);
    }

    /** How one point relates a row's value to what it is against, or null where none is owed. */
    public String operator(PointRole role) {
        souther.compiler.partition.Criterion criterion = border.demand(role).criterion();
        return criterion == null ? null : criterion.operator();
    }

    /** What that point is against, or null where none is owed. */
    public String against(PointRole role) {
        souther.compiler.partition.Criterion criterion = border.demand(role).criterion();
        // Asked of the criterion, which is what knows whether it is written against a level or
        // against a run of them. Two of the four points name a level and two name a run, and a
        // reader that took a level from every shape wrote a value inside a run as though it were
        // the run.
        return criterion == null ? null : criterion.written(border.cut().of());
    }

    /** The left of the {@code left = right} a report names this line by. */
    public String left() {
        return border.cut().left();
    }

    /** The right of it, which for a line between two positions is the other position. */
    public String value() {
        return border.cut().right();
    }

    /**
     * One coverage item of one border, for a reader that walks the items rather than the borders.
     *
     * <p>One place turns borders into items, so that a count, a document, a finding and the rows a
     * tool offers are four readings of one list. Flattened separately by each of them, a reader that
     * forgot a role would silently be short by it — which is the shape this whole measure was in
     * before the border owed its four.
     */
    public record Point(BorderAssessment border, PointRole role, ItemAssessment item) {

        /** What a row here would be written as, or null where none is owed. */
        public String label() {
            return border.label(role);
        }

        /** What this asks of a row, as a report writes it, or null where none is owed. */
        public String asked() {
            return border.operator(role) == null ? null
                    : border.operator(role) + " " + border.against(role);
        }

        /** What the point is against, or null where none is owed. */
        public String against() {
            return border.against(role);
        }

        /** The measured half, or null where no row is owed here. */
        public ItemAssessment.Owed owed() {
            return item instanceof ItemAssessment.Owed owed ? owed : null;
        }
    }

    /** Every one of this border's four items, in role order. */
    public java.util.List<Point> points() {
        return EnumSet.allOf(PointRole.class).stream()
                .map(role -> new Point(this, role, at(role))).toList();
    }

    /** The same over a list of borders. */
    public static java.util.List<Point> pointsOf(java.util.List<BorderAssessment> borders) {
        return borders.stream().flatMap(each -> each.points().stream()).toList();
    }

    /** The roles a row is owed in, which is what a coverage count is over. */
    public java.util.List<PointRole> owed() {
        return EnumSet.allOf(PointRole.class).stream().filter(role -> at(role).owed()).toList();
    }

    /** The roles the model's own rules discharged, which a report counts as excluded rather than as
     *  items nobody has got to. */
    public java.util.List<PointRole> excluded() {
        return EnumSet.allOf(PointRole.class).stream()
                .filter(role -> border.demand(role).excluded()).toList();
    }
}
