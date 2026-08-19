package souther.compiler.partition;

import souther.compiler.inputs.BoundaryDomain;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;

import java.util.EnumMap;
import java.util.EnumSet;
import java.util.Map;
import java.util.Optional;

/**
 * One line a rule drew, and what a row is owed at each of its four points.
 *
 * <p>The unit the technique keys on. Domain testing asks for an {@code ON}, an {@code OFF}, an
 * {@code IN} and an {@code OUT} point per border, and the same value can be one role for one border
 * and another role for the next — so what owes the four is a border, and nothing else can be asked.
 * Two of the four used to be answered here as separate obligations, and the other two by the measure
 * that counts how many of a position's classes some row is in: one technique's items split across two
 * units, only one of which a report could say anything about a border with.
 *
 * <p><b>Total over {@link PointRole}.</b> Every border answers for every role, and the answer for a
 * role nobody is owed a row in is a reason ({@link Demand.NotOwed}) rather than an entry left out.
 * That is checked here and not by a test: the entries used to be built by a loop that added an
 * obligation where it had one and did nothing where it did not, so four different facts — the rules
 * refusing the far side, a carrier with no next value, a side one value wide, a rule that names a
 * value instead of a side — all arrived as a shorter list. A role that goes missing now stops the
 * build where the border is made.
 *
 * <p>Which rule drew it is {@link #origin}'s, which reading of that rule this is is the origin's too,
 * and which of those readings are one line is {@link BoundaryLine}'s. This is not a fourth identity:
 * a border is a line together with what it owes, and two readings of one line owe the same four
 * things.
 *
 * @param cut     where the line is. Its own shape says how to read it — a place of one position, or
 *                the relation between two of them
 * @param origin  the rule that drew it, as this reading met it
 * @param demands one entry per role, always four of them
 */
public record Border(BoundaryTarget cut, OriginRef origin, Map<PointRole, Demand> demands) {

    public Border {
        if (demands == null || !demands.keySet().equals(EnumSet.allOf(PointRole.class))) {
            throw new IllegalArgumentException(
                    "a border that does not answer for every point role: " + demands);
        }
        demands = java.util.Collections.unmodifiableMap(new EnumMap<>(demands));
    }

    /** What this border asks of the rows in one role. */
    public Demand demand(PointRole role) {
        return demands.get(role);
    }

    /** Where the line is, as a report names it. Not what any one of its points asks for: that is
     *  {@link #label(PointRole)}, and the two differ at three of the four. */
    public String label() {
        return cut.left() + " = " + cut.right();
    }

    /**
     * How a row at one point of this border describes itself.
     *
     * <p>What the generator writes on the row it offers, so that a row and the note about the point
     * it stands for name it the same way. Null where nothing is owed in this role — there is no row
     * to label.
     */
    public String label(PointRole role) {
        Criterion criterion = demand(role).criterion();
        return criterion == null ? null : cut.left() + " " + criterion.asked(cut);
    }

    /**
     * The border a rule drew at one place of one position, or null where the position does not reach
     * the line.
     *
     * <p>Null is the line and not one of its points. A rule draws where it draws about the type, and
     * what the record holding the position leaves may stop short of it — {@code low < high} under one
     * {@code [0, 1]} leaves {@code low} every value up to 1 and not 1 itself. There is no border at
     * this position then, and there never was one for a point to be owed at: a reading that dropped
     * the value and went on to ask for the value beside it produced a border with an {@code OFF}
     * point and no {@code ON} point, which is not a shape the technique has.
     *
     * <p>Asked of the place rather than of the value, so every carrier is asked the same question.
     * Asked of the value, a date came back as one the range could say nothing about, which read as
     * reachable and put a row at an edge the record refuses.
     */
    public static Border atAPlace(AxisId axis, Cut cut, OriginRef origin, BoundaryDomain domain,
                                  NumericDomain.Bounds within) {
        NumericDomain.Bounds reach = within == null ? new NumericDomain.Bounds(null, null) : within;
        Place at = cut.at();
        if (!reach.admits(at)) {
            return null;
        }
        boolean holdsHere = holdsAtTheValue(origin);
        // Which of the two points the line's own value serves as, and which one the value beside it
        // serves as. The same `at` is the ON point of `<= 3000` and the OFF point of `< 3000`, so
        // this turns on whether the rule is satisfied where the line is and on nothing else.
        PointRole roleAtTheCut = holdsHere ? PointRole.ON : PointRole.OFF;
        PointRole roleBesideTheCut = holdsHere ? PointRole.OFF : PointRole.ON;
        Demand besideTheCut = besideTheCut(origin, at, domain, reach);

        Map<PointRole, Demand> demands = new EnumMap<>(PointRole.class);
        demands.put(roleAtTheCut, new Demand.Owed(new Criterion.AtThePlace(at)));
        demands.put(roleBesideTheCut, besideTheCut);
        Region.Towards beside = towardsTheValueBesideTheCut(origin);
        if (beside == null) {
            sidesOfAOneSidedLine(demands, origin, at, holdsHere, reach);
        } else {
            // Each side runs from the point against the line on that side, where there is one, and
            // from the line itself where there is not: the values one step away are not there to be
            // left out, and everything past the line is then as far from the border as anything
            // gets.
            Region.Towards inside = holdsHere ? opposite(beside) : beside;
            demands.put(PointRole.IN, sideOf(new Region.Beyond(
                    placeOf(demands.get(PointRole.ON), at), inside), reach));
            demands.put(PointRole.OUT, sideOf(new Region.Beyond(
                    placeOf(demands.get(PointRole.OFF), at), opposite(inside)), reach));
        }
        return new Border(new BoundaryTarget.AtPlace(axis, cut.carrier(), at), origin, demands);
    }

    /**
     * The two sides of a line that has only one, which the two rules that draw one answer opposite
     * ways.
     *
     * <p>Neither side is a run of the order from anywhere, so both are written as what the position
     * admits other than the point — and which role that set belongs to is the whole of the difference.
     * A bound leaves everything else <em>inside</em> it, because nothing outside can be constructed
     * at all. An equality leaves everything else <em>outside</em>, because what it distinguishes is
     * the one value from every other one. Read as one case, a bound's whole admitted range was
     * offered as the {@code OUT} point of a border nothing can be outside of.
     */
    private static void sidesOfAOneSidedLine(Map<PointRole, Demand> demands, OriginRef origin,
                                             Place at, boolean holdsHere,
                                             NumericDomain.Bounds within) {
        Region rest = new Region.AdmittedOtherThan(at);
        switch (noSideOf(origin)) {
            case THE_RULES_REFUSE_IT -> {
                if (!holdsHere) {
                    // A bound the position does not admit its own cut value at draws no border, and
                    // that is settled above. Reaching here is the reader of what a position admits
                    // and the reader of where a bound stops disagreeing about one rule.
                    throw new IllegalStateException(
                            "a bound whose own value the position admits and the bound does not: "
                                    + origin.named());
                }
                demands.put(PointRole.IN, sideOf(rest, within));
                demands.put(PointRole.OUT, new Demand.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT));
            }
            case THE_RULE_NAMES_A_VALUE_NOT_A_SIDE -> {
                // The value's own class is the value, so the side the cut is on has nothing away
                // from the border; the rest of the position is the other side. `x == 5` puts the cut
                // inside and `x /= 5` puts it outside, which is what `holdsHere` says.
                PointRole ofTheRest = holdsHere ? PointRole.OUT : PointRole.IN;
                demands.put(ofTheRest, sideOf(rest, within));
                demands.put(ofTheRest == PointRole.OUT ? PointRole.IN : PointRole.OUT,
                        new Demand.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT));
            }
            // A carrier with no next value leaves the line its second side; it is the value on that
            // side it has no name for, which is the point beside the cut and not the side itself.
            case THE_CARRIER_NAMES_NO_NEIGHBOUR -> throw new IllegalStateException(
                    "a line with no second side because of the carrier: " + origin.named());
        }
    }

    /**
     * The border a rule drew where two positions hold one place.
     *
     * <p>The same four roles and none of them read off an axis. The line divides neither position, so
     * neither side of it is a set of one position's values — a row is inside it by writing two places
     * that stand in the right order, which is as much a coverage item as writing one place is. Left
     * to the measure that counts a position's classes, a line between two positions had no
     * {@code IN} point and no {@code OUT} point anywhere, because neither position has a class the
     * line drew.
     *
     * <p>What it has no room for is the point one step from the line. That step is on the difference
     * the two positions fall apart by, and no carrier names a neighbour there.
     *
     * @param onIsAboveWhereTheRuleHolds which way round the two terms stand where the comparison is
     *                                   satisfied, which is what the operator says and what a line
     *                                   holding only its own place cannot be asked
     */
    public static Border betweenTerms(BoundaryTarget.EqualTerms line, OriginRef origin,
                                      boolean onIsAboveWhereTheRuleHolds) {
        boolean holdsHere = holdsAtTheValue(origin);
        Region.Towards inside =
                onIsAboveWhereTheRuleHolds ? Region.Towards.ABOVE : Region.Towards.BELOW;
        Map<PointRole, Demand> demands = new EnumMap<>(PointRole.class);
        demands.put(holdsHere ? PointRole.ON : PointRole.OFF,
                new Demand.Owed(new Criterion.WhereTheTermsMeet()));
        demands.put(holdsHere ? PointRole.OFF : PointRole.ON,
                new Demand.NotOwed(NotOwedReason.THE_CARRIER_NAMES_NO_NEIGHBOUR));
        demands.put(PointRole.IN,
                new Demand.Owed(new Criterion.InTheRegion(new Region.TermsApart(inside))));
        demands.put(PointRole.OUT,
                new Demand.Owed(new Criterion.InTheRegion(new Region.TermsApart(opposite(inside)))));
        return new Border(line, origin, demands);
    }

    /**
     * The value beside the line, or why no row is owed there.
     *
     * <p>Three reasons and one row, and the three used to be one silence. Which rule drew the line
     * says whether the line has another side at all; the carrier says whether it names the value one
     * step over; and what the position admits says whether that value is one a row can be written at
     * — {@code value >= 10} under {@code x < 10} would otherwise be owed a 9 the record refuses.
     */
    private static Demand besideTheCut(OriginRef origin, Place at, BoundaryDomain domain,
                                       NumericDomain.Bounds within) {
        Region.Towards towards = towardsTheValueBesideTheCut(origin);
        if (towards == null) {
            return new Demand.NotOwed(noSideOf(origin));
        }
        Optional<Place> next = towards == Region.Towards.ABOVE
                ? domain.successor(at) : domain.predecessor(at);
        if (next.isEmpty()) {
            return new Demand.NotOwed(NotOwedReason.THE_CARRIER_NAMES_NO_NEIGHBOUR);
        }
        return within.admits(next.get())
                ? new Demand.Owed(new Criterion.AtThePlace(next.get()))
                : new Demand.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT);
    }

    /** A side of the border, or the reason the rules leave nothing there for a row to be at. */
    private static Demand sideOf(Region region, NumericDomain.Bounds within) {
        return region.provablyHoldsNothing(within)
                ? new Demand.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT)
                : new Demand.Owed(new Criterion.InTheRegion(region));
    }

    /** Where a side starts: the point against the line on that side, or the line where there is
     *  none. */
    private static Place placeOf(Demand against, Place line) {
        return against.criterion() instanceof Criterion.AtThePlace at ? at.place() : line;
    }

    private static Region.Towards opposite(Region.Towards towards) {
        return towards == Region.Towards.ABOVE ? Region.Towards.BELOW : Region.Towards.ABOVE;
    }

    /**
     * Which side of the cut the second point of this border is on, or null where the line has only
     * one.
     *
     * <p>Asked of the origin here rather than answered by it. Which rule drew a line and which side
     * of the line a row is owed on are two questions, and only the first is the rule's — the second
     * is what this measure does with the answer, and reading it off the origin put the vocabulary of
     * borders inside the identity every other measure of a rule shares.
     */
    private static Region.Towards towardsTheValueBesideTheCut(OriginRef origin) {
        return switch (origin) {
            case OriginRef.GuardOrigin g -> g.singles() ? null
                    : g.valueBelongsBelow() ? Region.Towards.ABOVE : Region.Towards.BELOW;
            case OriginRef.EnsuresOrigin e -> e.singles() ? null
                    : e.valueBelongsBelow() ? Region.Towards.ABOVE : Region.Towards.BELOW;
            case OriginRef.NarrowedOrigin n -> towardsTheValueBesideTheCut(n.bound());
            case OriginRef.InvariantOrigin _ -> null;
        };
    }

    /** Why a line has only one side, which is not the same answer for the two rules that leave it
     *  with one. */
    private static NotOwedReason noSideOf(OriginRef origin) {
        return switch (origin) {
            // Nothing outside a bound can be constructed, so the far side holds no value at all.
            case OriginRef.InvariantOrigin _ -> NotOwedReason.THE_RULES_REFUSE_IT;
            case OriginRef.NarrowedOrigin n -> noSideOf(n.bound());
            // A rule that singles a value out orders nothing around it, so neither neighbour is
            // nearer to being outside than the other.
            case OriginRef.GuardOrigin _, OriginRef.EnsuresOrigin _ ->
                    NotOwedReason.THE_RULE_NAMES_A_VALUE_NOT_A_SIDE;
        };
    }

    /** Whether the cut value itself satisfies the rule that drew the line. */
    private static boolean holdsAtTheValue(OriginRef origin) {
        return switch (origin) {
            case OriginRef.GuardOrigin g -> g.holdsAtTheValue();
            case OriginRef.EnsuresOrigin e -> e.holdsAtTheValue();
            case OriginRef.InvariantOrigin i -> i.holdsAtTheValue();
            case OriginRef.NarrowedOrigin n -> holdsAtTheValue(n.bound());
        };
    }
}
