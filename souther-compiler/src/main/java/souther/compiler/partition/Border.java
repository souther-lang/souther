package souther.compiler.partition;

import souther.compiler.numeric.Endpoint;
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
 * <p><b>One reading, whatever the rule cut.</b> Where the four points are is a question about the
 * order the quantity's own values sit on, and about nothing else — so a bound on a position, a rule
 * relating two positions and a rule over an arithmetic form are read here by one procedure. Written
 * as a procedure per shape of line, the two that existed answered the same question by different
 * reasoning and a third would have been a third reasoning.
 *
 * <p><b>Total over {@link PointRole}.</b> Every border answers for every role, and the answer for a
 * role nobody is owed a row in is a reason ({@link Demand.NotOwed}) rather than an entry left out.
 * That is checked here and not by a test: the entries used to be built by a loop that added an
 * obligation where it had one and did nothing where it did not, so four different facts — the rules
 * refusing the far side, an order with no next value, a side one value wide, a rule that names a
 * value instead of a side — all arrived as a shorter list. A role that goes missing now stops the
 * build where the border is made.
 *
 * <p>Which rule drew it is {@link #origin}'s, which reading of that rule this is is the origin's too,
 * and which of those readings are one line is {@link BoundaryLine}'s. This is not a fourth identity:
 * a border is a line together with what it owes, and two readings of one line owe the same four
 * things.
 *
 * @param cut     where the line is: what is cut, and where on it
 * @param origin  the rule that drew it, as this reading met it
 * @param demands one entry per role, always four of them
 */
public record Border(BoundaryTarget cut, OriginRef origin, Map<PointRole, Demand> demands) {

    public Border {
        if (demands == null || !demands.keySet().equals(EnumSet.allOf(PointRole.class))) {
            throw new IllegalArgumentException(
                    "a border that does not answer for every point role: " + demands);
        }
        // And an answer at every one of them. A key with nothing under it is the same silence the
        // roles were made total to stop, wearing the shape that was supposed to have refused it.
        if (demands.containsValue(null)) {
            throw new IllegalArgumentException(
                    "a border with a point role it names and does not answer: " + demands);
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
        return criterion == null ? null : label(criterion);
    }

    /** The same of a criterion this border owes, for a caller that is holding one rather than a
     *  role. One spelling, so that what a search reports and what a report prints agree. */
    public String label(Criterion criterion) {
        return cut.left() + " " + criterion.asked(cut.of());
    }

    /**
     * The border a rule drew, or null where the quantity does not reach the line.
     *
     * <p>Null is the line and not one of its points. A rule draws where it draws about the type, and
     * what the record holding the position leaves may stop short of it — {@code low < high} under one
     * {@code [0, 1]} leaves {@code low} every value up to 1 and not 1 itself. There is no border
     * then, and there never was one for a point to be owed at: a reading that dropped the value and
     * went on to ask for the value beside it produced a border with an {@code OFF} point and no
     * {@code ON} point, which is not a shape the technique has.
     *
     * <p>Asked of the level rather than of the value, so every quantity is asked the same question.
     * Asked of the value, a date came back as one the range could say nothing about, which read as
     * reachable and put a row at an edge the record refuses.
     *
     * @param within what the rules leave the quantity, on the quantity's own order. Null where they
     *               leave it everything
     */
    public static Border at(BoundaryTarget target, OriginRef origin, NumericDomain.Bounds within) {
        NumericDomain.Bounds reach = within == null ? new NumericDomain.Bounds(null, null) : within;
        LevelSpace space = target.levels();
        Level cut = target.at();
        if (!reach.admits(placeOf(cut))) {
            return null;
        }
        boolean holdsHere = holdsAtTheValue(origin);
        Map<PointRole, Demand> demands = new EnumMap<>(PointRole.class);
        if (!ordersAroundTheCut(origin)) {
            // Which of the two points the line's own level serves as. A rule that leaves the line one
            // side has no second point, and the level it named is the point on the side it has.
            PointRole atTheCut = holdsHere ? PointRole.ON : PointRole.OFF;
            demands.put(atTheCut, new Demand.Owed(new Criterion.AtTheLevel(cut)));
            demands.put(atTheCut == PointRole.ON ? PointRole.OFF : PointRole.ON,
                    new Demand.NotOwed(noSideOf(origin)));
            sidesOfAOneSidedLine(demands, origin, cut, holdsHere, space, reach);
            return new Border(target, origin, demands);
        }
        // Which way the rule is satisfied from the threshold, which is the one thing the two points
        // are read off. The same `at` is the ON point of `<= 3000` and the OFF point of `< 3000`,
        // and neither is the threshold at all where the quantity does not take it.
        Towards satisfying = satisfyingSide(origin);
        Demand on = pointAt(space, cut, satisfying, holdsHere, reach);
        Demand off = pointAt(space, cut, satisfying.opposite(), !holdsHere, reach);
        demands.put(PointRole.ON, on);
        demands.put(PointRole.OFF, off);
        // Each side runs from the point against the line on that side, where there is one, and from
        // the line itself where there is not: the values one step away are not there to be left out,
        // and everything past the line is then as far from the border as anything gets.
        demands.put(PointRole.IN,
                sideOf(new Criterion.Beyond(levelOf(on, cut), satisfying), space, reach));
        demands.put(PointRole.OUT,
                sideOf(new Criterion.Beyond(levelOf(off, cut), satisfying.opposite()), space, reach));
        return new Border(target, origin, demands);
    }

    /**
     * One of the two points of a line the rule orders the values around, or why no row is owed there.
     *
     * <p>Three reasons and one row, and the three used to be one silence. Whether the threshold is a
     * level the quantity takes says whether either point is at the threshold itself; the order says
     * whether it names a value the way this point lies; and what the rules leave says whether that
     * level is one a row can be written at — {@code value >= 10} under {@code x < 10} would otherwise
     * be owed a 9 the record refuses.
     *
     * @param isTheThreshold whether this point is the threshold itself, where the quantity takes it
     */
    private static Demand pointAt(LevelSpace space, Level cut, Towards towards,
                                  boolean isTheThreshold, NumericDomain.Bounds reach) {
        if (isTheThreshold && space.attainable(cut)) {
            // Admitted already: a threshold the rules refuse is a line this never made.
            return new Demand.Owed(new Criterion.AtTheLevel(cut));
        }
        Optional<Level> at = beyond(space, cut, towards);
        if (at.isEmpty()) {
            return new Demand.NotOwed(NotOwedReason.THE_CARRIER_NAMES_NO_NEIGHBOUR);
        }
        return reach.admits(placeOf(at.get()))
                ? new Demand.Owed(new Criterion.AtTheLevel(at.get()))
                : new Demand.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT);
    }

    /**
     * The nearest level the quantity takes on one side of the threshold.
     *
     * <p>The value beside the threshold where the quantity takes the threshold, and the first value
     * it does take otherwise. Two questions the order answers apart: {@code 2 * a <= 9} has no
     * neighbour of 9 to ask for, because 9 is not a level it stands at, and the level it stands at
     * below 9 is not one step from anything.
     */
    private static Optional<Level> beyond(LevelSpace space, Level cut, Towards towards) {
        return space.attainable(cut) ? space.neighbour(cut, towards)
                : space.nearestAtOrBeyond(cut, towards);
    }

    /**
     * The two sides of a line that has only one, which the two rules that draw one answer opposite
     * ways.
     *
     * <p>Neither side is a run of the order from anywhere, so both are written as what the quantity
     * takes other than the point — and which role that set belongs to is the whole of the difference.
     * A bound leaves everything else <em>inside</em> it, because nothing outside can be constructed
     * at all. An equality leaves everything else <em>outside</em>, because what it distinguishes is
     * the one value from every other one. Read as one case, a bound's whole admitted range was
     * offered as the {@code OUT} point of a border nothing can be outside of.
     */
    private static void sidesOfAOneSidedLine(Map<PointRole, Demand> demands, OriginRef origin,
                                             Level cut, boolean holdsHere, LevelSpace space,
                                             NumericDomain.Bounds within) {
        Criterion rest = new Criterion.AnythingBut(cut);
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
                demands.put(PointRole.IN, sideOf(rest, space, within));
                demands.put(PointRole.OUT, new Demand.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT));
            }
            case THE_RULE_NAMES_A_VALUE_NOT_A_SIDE -> {
                // The value's own class is the value, so the side the cut is on has nothing away
                // from the border; the rest of the quantity is the other side. `x == 5` puts the cut
                // inside and `x /= 5` puts it outside, which is what `holdsHere` says.
                PointRole ofTheRest = holdsHere ? PointRole.OUT : PointRole.IN;
                demands.put(ofTheRest, sideOf(rest, space, within));
                demands.put(ofTheRest == PointRole.OUT ? PointRole.IN : PointRole.OUT,
                        new Demand.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT));
            }
            // An order with no next value leaves the line its second side; it is the value on that
            // side it has no name for, which is the point beside the cut and not the side itself.
            case THE_CARRIER_NAMES_NO_NEIGHBOUR -> throw new IllegalStateException(
                    "a line with no second side because of the order: " + origin.named());
        }
    }

    /** A side of the border, or the reason the rules leave nothing there for a row to be at. */
    private static Demand sideOf(Criterion side, LevelSpace space, NumericDomain.Bounds within) {
        return provablyHoldsNothing(side, space, within)
                ? new Demand.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT)
                : new Demand.Owed(side);
    }

    /**
     * Whether the order and the rules together leave a side no level at all, where that can be
     * settled.
     *
     * <p>A proof and never a search that came up empty. Two facts and both of them proofs: the order
     * itself may stop there — an enumeration at its last case — and the rules may have crossed. A
     * side a search could not compose a value in is a different account and is
     * {@link Realization}'s to give; read as emptiness it would take a coverage item away on the
     * strength of what this compiler can build.
     *
     * <p>Not asked of adjacency. A side with no <em>next</em> value is not a side with no value:
     * every pair of decimals further apart than a line is a pair, and reading the missing step as a
     * missing side took the {@code IN} point off every border over them.
     */
    private static boolean provablyHoldsNothing(Criterion side, LevelSpace space,
                                                NumericDomain.Bounds within) {
        return switch (side) {
            case Criterion.Beyond beyond -> {
                if (!space.anythingBeyond(beyond.from(), beyond.towards())) {
                    yield true;
                }
                Endpoint past = Endpoint.exclusive(placeOf(beyond.from()));
                Endpoint low = beyond.towards() == Towards.ABOVE
                        ? Endpoint.lower(past, within.min()) : within.min();
                Endpoint high = beyond.towards() == Towards.BELOW
                        ? Endpoint.upper(past, within.max()) : within.max();
                yield !Endpoint.someValueLiesBetween(low, high);
            }
            // Both ends known, at the one place, and holding it: the rules leave that level and
            // nothing else, so there is nothing else for a row to be written at.
            case Criterion.AnythingBut other -> within.min() != null && within.max() != null
                    && within.min().inclusive() && within.max().inclusive()
                    && within.min().at().sameAs(placeOf(other.excluded()))
                    && within.max().at().sameAs(placeOf(other.excluded()));
            case Criterion.AtTheLevel _ -> false;
        };
    }

    /** Where a side starts: the point against the line on that side, or the line where there is
     *  none. */
    private static Level levelOf(Demand against, Level line) {
        return against.criterion() instanceof Criterion.AtTheLevel at ? at.at() : line;
    }

    /**
     * A level as a place on the order it is a level of.
     *
     * <p>The one narrowing, so that what the rules leave — which is written as places, because it is
     * read off the declarations — can be held against what the quantity takes. Both are on the
     * quantity's own order by construction: the bounds handed in are the bounds of the thing being
     * cut, and a caller that handed in a position's bounds for a border over something else would be
     * answering a different question here as well.
     */
    private static Place placeOf(Level level) {
        return switch (level) {
            case Level.OnACarrier on -> on.at();
            case Level.ACount count -> count.at();
        };
    }

    /**
     * Which way from the threshold the rule is satisfied.
     *
     * <p>Derived here from the two things a rule says about its own threshold, rather than asked of
     * each producer. Which side the threshold's own value belongs to and whether the rule holds there
     * are what every rule records ({@link OriginRef}); which way the rule is satisfied follows from
     * the pair and is what a border is read off. Recorded a third time it would be free to disagree
     * with them, and a line whose sides were the wrong way round asks for two rows that prove
     * nothing.
     */
    private static Towards satisfyingSide(OriginRef origin) {
        return holdsAtTheValue(origin) == valueBelongsBelow(origin) ? Towards.BELOW : Towards.ABOVE;
    }

    /**
     * Whether the rule orders the values around its threshold at all.
     *
     * <p>Asked of the origin here rather than answered by it. Which rule drew a line and whether that
     * line has two sides are two questions, and only the first is the rule's — the second is what
     * this measure does with the answer, and reading it off the origin put the vocabulary of borders
     * inside the identity every other measure of a rule shares.
     */
    private static boolean ordersAroundTheCut(OriginRef origin) {
        return switch (origin) {
            case OriginRef.GuardOrigin g -> !g.singles();
            case OriginRef.EnsuresOrigin e -> !e.singles();
            case OriginRef.NarrowedOrigin n -> ordersAroundTheCut(n.bound());
            case OriginRef.InvariantOrigin _ -> false;
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

    /** Whether the threshold's own value satisfies the rule that drew the line. */
    private static boolean holdsAtTheValue(OriginRef origin) {
        return switch (origin) {
            case OriginRef.GuardOrigin g -> g.holdsAtTheValue();
            case OriginRef.EnsuresOrigin e -> e.holdsAtTheValue();
            case OriginRef.InvariantOrigin i -> i.holdsAtTheValue();
            case OriginRef.NarrowedOrigin n -> holdsAtTheValue(n.bound());
        };
    }

    /** Which side of the line the threshold's own value belongs to. */
    private static boolean valueBelongsBelow(OriginRef origin) {
        return switch (origin) {
            case OriginRef.GuardOrigin g -> g.valueBelongsBelow();
            case OriginRef.EnsuresOrigin e -> e.valueBelongsBelow();
            case OriginRef.InvariantOrigin _ -> false;
            case OriginRef.NarrowedOrigin n -> valueBelongsBelow(n.bound());
        };
    }
}
