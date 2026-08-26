package souther.compiler.partition;

import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Towards;

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

    /**
     * What a row here is owed for, which several readings of this line share.
     *
     * <p>The line the author wrote, without the position it was read at. Everything that folds
     * readings together keys on this; everything that says where a row would go reads {@link #cut}.
     * Both are here rather than one being worked out from the other by whoever needs it, because a
     * caller deriving a key from the parts it happened to know is how one clause's row came to be
     * asked for once per position of every behavior carrying the type (issue #1062).
     */
    public BorderObligationId obligation() {
        return new BorderObligationId(origin, cut.at());
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
        // A run names the quantity itself, because that is how a range of it reads — `10 < n <= 20`
        // and not `n in 10 < n <= 20`. The two shapes that name a level do not, so the quantity is
        // written in front of them here.
        return criterion instanceof Criterion.Within
                ? criterion.written(cut.of())
                : cut.left() + " " + criterion.asked(cut.of());
    }

    /**
     * The border a rule drew.
     *
     * <p>Total. Whether the quantity reaches the line at all is {@link #reaches}, asked before this
     * by whoever holds the rule, and a caller here has already had that answer — so there is no
     * second reading of it and no way for one to come back empty. It used to be answered twice, and
     * the answer here was a null the two callers dropped without a word: a rule of the model went
     * unmeasured, nothing recorded that it had, and the measure came back saying the behavior's
     * rules draw no line anywhere (issue #1079).
     *
     * <p><b>Where the rule stops is not where a row is written.</b> The two are one value on a
     * carrier that steps, because a strict end is moved onto the value it leaves before it ever gets
     * here — {@code value > 5} on an {@code Int} arrives as an inclusive 6. A carrier with no step
     * has no such move, so {@code value > 5.0m} arrives as an exclusive 5, and the point against
     * that line is a value the order cannot name. Both are lines. Which value each of the four
     * points stands at is asked of the order below, and never read off the cut.
     *
     * @param within what the rules leave the quantity, on the quantity's own order. Null where they
     *               leave it everything
     */
    public static Border at(BoundaryTarget target, OriginRef origin, NumericDomain.Bounds within) {
        return at(target, origin, within, java.util.List.of());
    }

    /**
     * The same, told where else the rules part this quantity's values.
     *
     * <p>Which is what the two points away from the line are read off. An {@code IN} point is inside
     * the partition this border bounds; read as everything past the line, it runs to the end of the
     * order, and a row past the next line along answers for it while the partition between them has
     * nothing in it (issue #880). The two are the same only where the quantity has one line through
     * it, which is why nothing noticed for as long as a border was built one rule at a time.
     *
     * @param parted every place the rules part this quantity's values, this border's own among them
     *               or not
     */
    public static Border at(BoundaryTarget target, OriginRef origin, NumericDomain.Bounds within,
                            java.util.List<Seam> parted) {
        NumericDomain.Bounds reach = within == null ? new NumericDomain.Bounds(null, null) : within;
        LevelSpace space = target.levels();
        Level cut = target.at();
        if (!reaches(target, within)) {
            // Asked and answered by whoever holds the rule. Reaching here is that reader and this
            // one disagreeing about one line, which is not a state a model can put them in.
            throw new IllegalStateException(
                    "a border built on a line the quantity does not reach: " + target.left()
                            + " at " + target.right());
        }
        Seam mine = parts(target, origin);
        java.util.List<Seam> all = new java.util.ArrayList<>(parted);
        if (mine != null && all.stream().noneMatch(each -> each.key().equals(mine.key()))) {
            all.add(mine);
        }
        QuantityArrangement arrangement = QuantityArrangement.of(space, all,
                endOf(space, reach.min(), Towards.ABOVE, cut),
                endOf(space, reach.max(), Towards.BELOW, cut));
        boolean holdsHere = holdsAtTheValue(origin);
        Map<PointRole, Demand> demands = new EnumMap<>(PointRole.class);
        if (!ordersAroundTheCut(origin)) {
            aLineWithOneSide(demands, origin, cut, holdsHere, space, reach, arrangement);
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
        // The partition this border bounds and the one it keeps out, each without the value against
        // the line — which is that side's own ON or OFF point and is not this one. A side the rules
        // leave nothing in is not a run of the arrangement at all, and that is the answer here too.
        // Each of the two is told which line it is named for: this border's own, which the run it
        // asks for lies one way of. The `IN` point is inside the partition this border bounds, so
        // the run runs the way the rule is satisfied; the `OUT` point is the other way. Worked out
        // from the run instead, the two points that share a run — this border's `IN` and the next
        // border's `OUT` — both started at the same end of it.
        demands.put(PointRole.IN, runOf(space, satisfying == Towards.ABOVE
                ? arrangement.above(mine) : arrangement.below(mine), against(on), satisfying));
        demands.put(PointRole.OUT, runOf(space, satisfying == Towards.ABOVE
                ? arrangement.below(mine) : arrangement.above(mine), against(off),
                satisfying.opposite()));
        return new Border(target, origin, demands);
    }

    /**
     * Whether the quantity reaches the line at all, which is the one thing about a border that does
     * not depend on the lines beside it.
     *
     * <p>Asked before the lines of one quantity are collected, because a rule that draws nothing has
     * to be reported as drawing nothing rather than joining the arrangement: three times a length is
     * never negative, and a rule comparing one against a negative draws no line for anything to be
     * beside.
     *
     * <p><b>Whether the line is outside what the rules leave, and not whether they leave its own
     * value.</b> A bound's line stands at the very end of what the bound leaves, and a strict one on
     * a carrier with no step stands at a value the position does not hold — the quantity comes
     * arbitrarily close to it and never arrives, which is a line with values on one side of it and
     * not a line nothing reaches. Asked as {@code admits}, the two were one answer: every strict
     * bound on a {@code Decimal} was read as drawing no line, and a model whose every rule was one
     * came back adequate on the strength of no measure at all (issue #1079).
     */
    public static boolean reaches(BoundaryTarget target, NumericDomain.Bounds within) {
        if (within == null) {
            return true;
        }
        Place at = placeOf(target.at());
        return (within.min() == null || at.compareTo(within.min().at()) >= 0)
                && (within.max() == null || at.compareTo(within.max().at()) <= 0);
    }

    /**
     * Every border the lines of one behavior draw, each told about the others on its own quantity.
     *
     * <p>One place, so that a quantity is arranged once however many rules cut it. Grouped by what
     * the rule cuts and not by how it was written: a form and any positive multiple of it order the
     * rows the same way, so they are one quantity and their lines are one arrangement.
     */
    public static java.util.List<Border> allOf(java.util.List<LineDrawn> drawn) {
        return allOf(drawn, java.util.Map.of());
    }

    /**
     * The same, told where else the rules of this behavior part the quantities these lines are on.
     *
     * <p>Because a quantity is arranged once and not once per producer. A line that divides a
     * position leaves its border on the position and its division on the axis; a line that divides
     * one and has no value there leaves its border here. Read apart, the second knew only its own
     * line — a rule cutting at a third beside a rule cutting at a fifth asked for a row anywhere at
     * all, twice — and the first knew both only because the axis happened to carry them.
     *
     * @param alsoParted where the rules part each quantity, in the quantity's own units, by
     *                   {@link QuantityKey#key}
     */
    public static java.util.List<Border> allOf(java.util.List<LineDrawn> drawn,
                                               java.util.Map<String,
                                                       java.util.List<Seam>> alsoParted) {
        // Collected in the quantity's own units, because that is the only order the lines of one
        // quantity are all on. Two rules can write one quantity at two scales — `3a + 6b > 48` and
        // `a + 2b > 20` run the same way — and the numbers they carry are not comparable until both
        // are read as what they are a multiple of.
        java.util.Map<String, java.util.List<Seam>> byQuantity = new java.util.LinkedHashMap<>();
        alsoParted.forEach((key, parted) ->
                byQuantity.computeIfAbsent(key, _ -> new java.util.ArrayList<>()).addAll(parted));
        for (LineDrawn each : drawn) {
            if (!ordersAroundTheCut(each.by())) {
                continue;
            }
            Seam parts = each.cuts().seam();
            java.util.List<Seam> already = byQuantity.computeIfAbsent(
                    each.cuts().quantity().key(), _ -> new java.util.ArrayList<>());
            if (already.stream().noneMatch(had -> had.key().equals(parts.key()))) {
                already.add(parts);
            }
        }
        java.util.List<Border> out = new java.util.ArrayList<>();
        for (LineDrawn each : drawn) {
            // And read back into the units this rule wrote, which is what its own quantity measures
            // a row in. A border reads rows through the form it was written as, so a run handed to
            // it in another scale would be held against numbers of a different size.
            java.math.BigDecimal per = each.cuts().per();
            java.util.List<Seam> beside =
                    byQuantity.getOrDefault(each.cuts().quantity().key(), java.util.List.of())
                            .stream().map(seam -> seam.scaledBy(per)).toList();
            // One line drawn, one border. Which lines there are was settled by whoever read the
            // rules — a comparison whose line the quantity does not reach is no line, and says so
            // there ({@code ComparisonAssessment.OutsideTheDomain}) — so nothing here decides it
            // again and nothing is dropped for having come back empty.
            Border made = at(each.cuts().target(), each.by(), each.cuts().within(), beside);
            if (out.stream().noneMatch(had -> had.equals(made))) {
                out.add(made);
            }
        }
        return java.util.List.copyOf(out);
    }

    /**
     * Where the rule this reading met parts the quantity's values.
     *
     * <p>For a caller collecting every place one quantity is parted before any border is built. A
     * border's two points away from the line are runs of the arrangement those places make, so a
     * border built without them knows only its own line and reads each side to the end of the order.
     */
    public static Seam parts(BoundaryTarget target, OriginRef origin) {
        // Null for a rule that orders nothing around its line. A bound is where the quantity stops
        // and not a place its values part — nothing outside one can be constructed, so there is no
        // run on the far side (ADR-0090) — and a rule that singles a value out puts every other
        // value on one side of it, which is not a run of the order either.
        if (!ordersAroundTheCut(origin)) {
            return null;
        }
        return Seam.of(target.levels(), target.at(),
                valueBelongsBelow(origin) ? Towards.BELOW : Towards.ABOVE);
    }

    /**
     * A row anywhere in one run but at the value against the line, or the reason the rules leave no
     * run there.
     *
     * <p>Whether anything is left is the order's answer about the item's own values, and not a
     * reading of where the run starts and stops: the rules may leave a side one value wide and that
     * value be the border's own point, and they may leave a run between two lines that the quantity
     * takes no value in at all. Told apart by comparing the two ends instead, the second was owed a
     * row nobody can write and the report said the search stopped looking for it.
     */
    private static Demand runOf(LevelSpace space, Band run, Level except, Towards away) {
        if (run == null) {
            return new Demand.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT);
        }
        Criterion.Within inside = new Criterion.Within(run, except, away);
        return inside.region().parts().stream().anyMatch(part -> space.inspect(part).any())
                ? new Demand.Owed(inside)
                : new Demand.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT);
    }

    /** The level a point against the line stands at, or null where no row is owed there. */
    private static Level against(Demand point) {
        return point.criterion() instanceof Criterion.AtTheLevel at ? at.at() : null;
    }

    /**
     * The first or last value the rules leave the quantity, from the end they wrote.
     *
     * <p>A value the quantity takes rather than the number a bound carries: a bound the quantity
     * does not stand at leaves the first value it does, and a bound it stands at but does not keep
     * leaves the one beside it.
     */
    private static Bound endOf(LevelSpace space, Endpoint end, Towards inward, Level like) {
        if (end == null) {
            return null;
        }
        Level at = like instanceof Level.OnACarrier on
                ? new Level.OnACarrier(on.of(), end.at())
                : new Level.ACount(souther.compiler.numeric.Count.number(end.at()));
        Optional<Level> value = end.inclusive() ? space.nearestAtOrBeyond(at, inward)
                : beyond(space, at, inward);
        if (value.isPresent()) {
            return Bound.at(value.get(), true);
        }
        // A strict end the quantity takes no first value past. The run stops where the rule stops
        // and does not keep the place it stops at, which is what the two together say: read as no
        // end at all, such a run ran to the end of the order and held every value the bound
        // refuses; read as the value, it held the one value the bound refuses.
        return end.inclusive() ? null : Bound.at(at, false);
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
    private static void aLineWithOneSide(Map<PointRole, Demand> demands, OriginRef origin,
                                         Level cut, boolean holdsHere, LevelSpace space,
                                         NumericDomain.Bounds within,
                                         QuantityArrangement arrangement) {
        Criterion rest = new Criterion.AnythingBut(cut);
        switch (noSideOf(origin)) {
            case THE_RULES_REFUSE_IT -> {
                // Which way the bound keeps its values, taken from the end of what the rules leave
                // that this line is: a bound orders nothing around itself, so there is no side to
                // read off the rule, and its line is where what it leaves stops.
                Towards kept = keptBy(within, cut);
                if (kept == null) {
                    // The reader of where a bound stops and the reader of what the position is left
                    // with disagreeing about one rule. A bound's line is an end of what it leaves,
                    // and a line inside that is not one this rule drew.
                    throw new IllegalStateException(
                            "a bound whose line is not an end of what it leaves: " + origin.named());
                }
                // The point against the line, asked of the order and never read off the cut. The
                // cut itself where the position holds it — which is every strict bound on a carrier
                // that steps, the end having been moved onto the value it leaves before it got here
                // — and the nearest value the rules leave otherwise. A carrier with no step names
                // none, and then the technique's point cannot be written down at all.
                Demand on = pointAt(space, cut, kept, holdsHere, within);
                demands.put(PointRole.ON, on);
                demands.put(PointRole.OFF, new Demand.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT));
                // The partition the bound bounds, without the value against the line. Everything
                // else was what this asked for before, which is every value the rules leave —
                // including the ones past the next line along, in a partition this border does not
                // bound.
                //
                // Found by the point and not by the cut, and short of a point by the cut. The two
                // are one level wherever the position holds the line's own value, and where it does
                // not the run starts past the cut: looked up by the cut, the run a bound leaves was
                // no run of the arrangement at all and its `IN` point came back refused.
                Level against = against(on) != null ? against(on) : cut;
                demands.put(PointRole.IN, runOf(space, arrangement.endmost(kept), against, kept));
                demands.put(PointRole.OUT, new Demand.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT));
            }
            case THE_RULE_NAMES_A_VALUE_NOT_A_SIDE -> {
                // The value the rule names, which is the one point against this line: a rule that
                // singles a value out orders nothing around it, so neither neighbour is nearer to
                // being outside than the other. Which of the two roles the value serves as is
                // whether the rule holds there — `x == 5` is met at five and `x /= 5` is not.
                PointRole atTheCut = holdsHere ? PointRole.ON : PointRole.OFF;
                demands.put(atTheCut, new Demand.Owed(new Criterion.AtTheLevel(cut)));
                demands.put(atTheCut == PointRole.ON ? PointRole.OFF : PointRole.ON,
                        new Demand.NotOwed(NotOwedReason.THE_RULE_NAMES_A_VALUE_NOT_A_SIDE));
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

    /**
     * Which way a bound keeps its values, from the end of what the rules leave that its line is.
     *
     * <p>Asked of what the rules leave rather than of the rule. A bound records where it stops and
     * not which side of that it keeps ({@link OriginRef.InvariantOrigin}), and it does not have to:
     * a bound's line is an end of what it leaves, so which end it is says which way the values run.
     *
     * <p>Null where the line is neither end, which is nothing a model can write. Where both ends are
     * the line — a rule leaving one value — either answer names the same point, and the low end is
     * taken.
     */
    private static Towards keptBy(NumericDomain.Bounds within, Level cut) {
        if (within == null) {
            return null;
        }
        Place at = placeOf(cut);
        if (within.min() != null && within.min().at().sameAs(at)) {
            return Towards.ABOVE;
        }
        return within.max() != null && within.max().at().sameAs(at) ? Towards.BELOW : null;
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
            // A run the rules leave nothing in is not a run of the arrangement, so nothing that
            // reaches here is one.
            case Criterion.Within _ -> false;
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
            case OriginRef.ComparisonOrigin g -> !g.singles();
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
            case OriginRef.ComparisonOrigin _, OriginRef.EnsuresOrigin _ ->
                    NotOwedReason.THE_RULE_NAMES_A_VALUE_NOT_A_SIDE;
        };
    }

    /** Whether the threshold's own value satisfies the rule that drew the line. */
    private static boolean holdsAtTheValue(OriginRef origin) {
        return switch (origin) {
            case OriginRef.ComparisonOrigin g -> g.holdsAtTheValue();
            case OriginRef.EnsuresOrigin e -> e.holdsAtTheValue();
            case OriginRef.InvariantOrigin i -> i.holdsAtTheValue();
            case OriginRef.NarrowedOrigin n -> holdsAtTheValue(n.bound());
        };
    }

    /** Which side of the line the threshold's own value belongs to. */
    private static boolean valueBelongsBelow(OriginRef origin) {
        return switch (origin) {
            case OriginRef.ComparisonOrigin g -> g.valueBelongsBelow();
            case OriginRef.EnsuresOrigin e -> e.valueBelongsBelow();
            case OriginRef.InvariantOrigin _ -> false;
            case OriginRef.NarrowedOrigin n -> valueBelongsBelow(n.bound());
        };
    }
}
