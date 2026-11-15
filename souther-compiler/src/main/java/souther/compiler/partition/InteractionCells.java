package souther.compiler.partition;

import souther.compiler.check.ComparisonClaim;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Towards;
import souther.compiler.observe.Figure;
import souther.compiler.observe.WorkFigure;
import souther.compiler.inputs.Requirements;
import souther.compiler.reading.Decision;
import souther.compiler.reading.Factor;
import souther.compiler.reading.Interaction;
import souther.compiler.reading.Outcome;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;

/**
 * The combinations a group of decisions has, as the classes a row filling one may sit in.
 *
 * <p>Two vocabularies meeting. A decision is read off the body and says which way a comparison came
 * out or which case a union was matched at; a row is written at classes of the input positions. The
 * two are about the same rules — the comparison a factor names is the comparison a cut was drawn
 * off — so this is a lookup rather than a second derivation of where the model divides.
 *
 * <p>A condition is a constraint and not a choice of class. {@code n > 10} leaves every class above
 * the line, and picking one of them here would answer for the condition alone and be wrong as soon
 * as a second one arrives: under {@code if n > 10 { if n > 0 { … } }} the way in is both, and a
 * reading that wrote a class down for each would keep the last. So a cell carries which classes each
 * position may hold, one condition narrows it, and a cell nothing is left at is not a combination.
 *
 * <p>What a combination is comes from the decisions it settles, and the classes only say where a
 * search looks for a row that settles them. So a decision the classes cannot place never takes a
 * combination away: it leaves the search region as wide as the classes cannot narrow it
 * ({@link Steering}), and the combination is still asked for. A row is credited with a combination
 * by what a run was seen doing ({@link CellSelection#certifying}) and never by where its values
 * sit, so a wide region costs a search more candidates and costs no false credit.
 *
 * <p>A region is a union of cells. A condition about a name the cases of a sum share is a cell under
 * each case, and the else of a conjunction is what is left outside it; one cell holds a product of
 * class sets and neither is one.
 */
public final class InteractionCells {

    private InteractionCells() {}

    /**
     * Which classes of each position a row may sit in, as far as something has said.
     *
     * @param allowed one flag per class of each position, in the order the axes are ordered
     */
    public record Cell(boolean[][] allowed) {

        /** Nothing said yet: every class of every position is still open. */
        public static Cell anything(List<Axis> axes) {
            boolean[][] allowed = new boolean[axes.size()][];
            for (int i = 0; i < axes.size(); i++) {
                allowed[i] = new boolean[axes.get(i).classes().size()];
                Arrays.fill(allowed[i], true);
            }
            return new Cell(allowed);
        }

        /** Both, or null where they leave a position nothing. */
        public Cell and(Cell other) {
            boolean[][] both = new boolean[allowed.length][];
            for (int i = 0; i < allowed.length; i++) {
                both[i] = allowed[i].clone();
                boolean any = false;
                for (int c = 0; c < both[i].length; c++) {
                    both[i][c] &= other.allowed[i][c];
                    any |= both[i][c];
                }
                if (!any && both[i].length > 0) {
                    return null;
                }
            }
            return new Cell(both);
        }

        /** Whether this says anything about the position, which is what a row is named for. */
        public boolean narrows(int axis) {
            for (boolean each : allowed[axis]) {
                if (!each) {
                    return true;
                }
            }
            return false;
        }

        public boolean admits(int axis, int cls) {
            return cls >= 0 && cls < allowed[axis].length && allowed[axis][cls];
        }

        /**
         * Whether a row sitting at {@code where} — one class per position, in the order the axes
         * are ordered — is one this leaves room for.
         *
         * <p>A position this says nothing about admits whatever the row has there. What it does not
         * admit is a class it narrowed away, which is the whole of what a cell is.
         */
        public boolean holds(int[] where) {
            for (int axis = 0; axis < allowed.length; axis++) {
                if (narrows(axis) && !(axis < where.length && admits(axis, where[axis]))) {
                    return false;
                }
            }
            return true;
        }

        public boolean sameAs(Cell other) {
            return Arrays.deepEquals(allowed, other.allowed);
        }

        /** The smallest cell holding every one of {@code cells}: each position the classes any of
         *  them leaves open. */
        static Cell hull(List<Cell> cells) {
            boolean[][] open = new boolean[cells.getFirst().allowed.length][];
            for (int i = 0; i < open.length; i++) {
                open[i] = new boolean[cells.getFirst().allowed[i].length];
                for (Cell each : cells) {
                    for (int c = 0; c < open[i].length; c++) {
                        open[i][c] |= each.allowed[i][c];
                    }
                }
            }
            return new Cell(open);
        }
    }

    /**
     * Where a search may look for a row that settles some decisions, and whether that is all the
     * rows that do.
     *
     * <p>A union of cells, which may overlap: what a combination is comes from its decisions and
     * not from how the region is cut, so the cells are only places to look.
     *
     * <p>Exact where every decision was read into classes, and otherwise a region that holds every
     * row that settles them and maybe more. A search of it is still sound — a row is certified by
     * what its run did — and its failure says nothing about whether the combination exists, which is
     * why an approximate region never makes one impossible. A region with no cell left is
     * impossible either way: what is wider than the rows that settle the decisions and holds none
     * of them leaves none.
     *
     * @param cells the cells, none of which leaves a position nothing
     * @param exact whether a row sits in one of them only where it settles the decisions
     */
    public record Steering(List<Cell> cells, boolean exact) {

        /** The most cells a region is kept as; a wider union is read as the one cell that holds it
         *  and is approximate. */
        private static final int MOST_CELLS = 32;

        public Steering {
            cells = List.copyOf(cells);
        }

        static Steering exactly(Cell cell) {
            return new Steering(List.of(cell), true);
        }

        /** Nothing said of the rows: every row, which is a region and not a fact. */
        static Steering unsaid(List<Axis> axes) {
            return new Steering(List.of(Cell.anything(axes)), false);
        }

        /** Rows in both, as a union of the cells they share. */
        Steering and(Steering other) {
            List<Cell> out = new ArrayList<>();
            for (Cell mine : cells) {
                for (Cell theirs : other.cells) {
                    Cell both = mine.and(theirs);
                    if (both != null && out.stream().noneMatch(both::sameAs)) {
                        out.add(both);
                    }
                }
            }
            return bounded(out, exact && other.exact);
        }

        /** Rows in either. */
        static Steering union(List<Steering> each) {
            List<Cell> out = new ArrayList<>();
            boolean exact = true;
            for (Steering one : each) {
                exact &= one.exact;
                for (Cell cell : one.cells) {
                    if (out.stream().noneMatch(cell::sameAs)) {
                        out.add(cell);
                    }
                }
            }
            return bounded(out, exact);
        }

        private static Steering bounded(List<Cell> cells, boolean exact) {
            return cells.size() > MOST_CELLS ? new Steering(List.of(Cell.hull(cells)), false)
                    : new Steering(cells, exact);
        }

        /** Whether no row settles these decisions. */
        boolean impossible() {
            return cells.isEmpty();
        }
    }

    /**
     * One combination of a group: where to look for a row that makes it, as a way for each cell of
     * its region, and whether the region is exact.
     *
     * <p>Every way holds a row to the same claims, so a combination made by a run is made whichever
     * cell the row was looked for in.
     */
    public record Choice(List<CellSelection> ways, boolean exact) {

        public Choice {
            ways = List.copyOf(ways);
        }
    }

    /**
     * What one way of settling something leaves open, what a run that settled it that way would be
     * seen to have done, and which decisions of the model that is.
     *
     * <p>The three travel together from here on. Kept apart, they would be lists indexed alike, and
     * an outcome dropped from one of them for narrowing nothing would leave the others saying what
     * a different outcome takes.
     *
     * <p>Each answers a different reader and none of them stands in for another. The classes are
     * where a search steers a candidate; the claims are what a run is held to; the decisions are
     * what the combination is, in the words the model states it in, and are what tells one
     * combination from every other.
     */
    public record Placed(Steering steering, List<souther.compiler.coverage.ControlClaim> claims,
                         List<souther.compiler.reading.Condition> settles) {

        public Placed {
            claims = List.copyOf(claims);
            settles = List.copyOf(settles);
        }
    }

    /**
     * One group's combinations, as somewhere to read them from rather than as a list.
     *
     * <p>Nothing is built until it is asked for. Which combinations get offered is the row budget's
     * to decide, and a list built beforehand would have to guess how much of it the budget reaches:
     * a combination a written row already sits in costs no row, so a caller that stopped enumerating
     * at the budget would leave the ones past that point untried while the budget still held.
     *
     * @param reach    what the path to the meeting leaves open, which every combination is under
     * @param byFactor what each outcome of each factor leaves open, one list per factor
     */
    public record Group(Placed reach, List<List<Placed>> byFactor) {

        public Group {
            byFactor = List.copyOf(byFactor);
        }

        /**
         * How many ways there are to choose one outcome from each factor.
         *
         * <p>Not how many combinations the group has: two factors reading one position have choices
         * that leave it nothing, and no row is written at those. This is the space the choices are
         * counted off, and {@link #at} says which of them are cells.
         *
         * <p>The product itself, with nothing to saturate at. A group exists only where {@link #of}
         * found the product within what the compilation allows, so the number fits an {@code int}
         * by having been checked before this was built — and a limit carried in here to be reached
         * would be the budget living on in a value the budget already admitted.
         */
        public int size() {
            int size = 1;
            for (List<Placed> factor : byFactor) {
                size *= factor.size();
            }
            return size;
        }

        /**
         * The {@code index}th choice as the cells a row for it is looked for in, or null where the
         * factors it takes leave a position nothing.
         *
         * <p>Leaving a position nothing is not a combination the body refuses. There is no path
         * through the body that takes both, so there is nothing there to ask for.
         */
        public Choice at(int index) {
            Steering steering = reach.steering();
            List<souther.compiler.coverage.ControlClaim> claims =
                    new ArrayList<>(reach.claims());
            int left = index;
            for (List<Placed> factor : byFactor) {
                Placed taken = factor.get(left % factor.size());
                steering = steering.and(taken.steering());
                if (steering.impossible()) {
                    return null;
                }
                claims.addAll(taken.claims());
                left /= factor.size();
            }
            return new Choice(steering.cells().stream()
                    .map(cell -> new CellSelection(cell, claims)).toList(), steering.exact());
        }

        /**
         * Which decisions the {@code index}th choice is: the way in and the outcome taken at each
         * factor, in the model's own words, as they were stated.
         *
         * <p>This is what the combination is; the cell beside it is that projected into the
         * classes a search steers by, and the claims are how a run is held to it. So a requirement
         * is named here and certified there, and a reading of the classes that is off moves where
         * a candidate is looked for without moving what is being asked for.
         *
         * <p>Handed as a list and not made a set here. What a run has to have done is a set — two
         * choices that come to the same decisions ask one thing of a row, however the way in and
         * the factors divided them up between them — and the caller makes it, with the hash of each
         * decision it already holds. A set made here would hash every decision of every choice
         * again, and a group of thousands of choices pays that thousands of times over for the
         * same few decisions.
         *
         * <p>Not told whether the choice is a combination: that is {@link #at}'s answer, and a
         * choice whose factors leave a position nothing is no combination the body has a path to.
         */
        public List<souther.compiler.reading.Condition> settlesAt(int index) {
            List<souther.compiler.reading.Condition> out = new ArrayList<>(reach.settles());
            int left = index;
            for (List<Placed> factor : byFactor) {
                out.addAll(factor.get(left % factor.size()).settles());
                left /= factor.size();
            }
            return out;
        }

        /** Whether the group has a combination at all, which stops at the first. */
        public boolean hasACombination() {
            for (int index = 0; index < size(); index++) {
                if (at(index) != null) {
                    return true;
                }
            }
            return false;
        }
    }

    /**
     * A group the limit kept from being offered, and what a run that took it would have been seen
     * to do.
     *
     * <p>The claims and not the cells. Which combinations the group has is the product this declined
     * to walk; which control points any of them could claim is the union over the way in and every
     * outcome of every factor, which is one pass over what {@link #factorsOf} already built. So the
     * arms behind the limit can be named without doing the work the limit exists to refuse.
     *
     * <p>A union and so a superset: no single combination claims all of these, and one of them may
     * be claimed by another group that was offered. A caller reads it for what is left owed after
     * every offered group has been searched, which is where the difference stops mattering.
     *
     * <p>And the conditions beside them, under the same union and for a different question. What a
     * requirement is told apart by is the decisions it settles a value by, so a reader holding one
     * can ask whether this group could have stated it — and a requirement none of whose conditions
     * this group has is one it certainly could not, whatever went unwalked. Without that, a group
     * held back leaves every requirement of every other group as one it might have stated.
     *
     * <p>And the limit it was held back by, as it stood where the group was compared against it:
     * how many combinations of one group are measured is handed to a run, so a reader is owed the
     * number this run used.
     */
    public record NotOffered(List<souther.compiler.coverage.ControlClaim> claims,
                             java.util.Set<souther.compiler.reading.Condition> settles,
                             Figure limit) {

        public NotOffered {
            claims = List.copyOf(claims);
            settles = java.util.Set.copyOf(settles);
            Objects.requireNonNull(limit, "a group held back was held back by a limit");
        }

        /**
         * Whether this group could have stated {@code settled}, as far as anything here can say.
         *
         * <p>True where every condition of the requirement is one this group has an outcome for.
         * That is not proof it states it — the product was never walked, and the conditions may
         * belong to combinations it has no path to — and it does not need to be: what a reader
         * wants is to be sure when the answer is no.
         */
        public boolean mightState(java.util.Set<souther.compiler.reading.Condition> settled) {
            return settles.containsAll(settled);
        }
    }

    /**
     * The groups to offer, and the ones the limit kept back.
     *
     * <p>Two answers because they are two facts and the second used to be neither returned nor
     * recorded. A group dropped for its width claims arms, and what was not walked at those arms is
     * something a caller says rather than something a reader has to notice going missing.
     *
     * <p>No third for the groups the classes cannot narrow: they are offered, over the region the
     * classes leave them, and a group is held back only for what the limit allows.
     */
    public record Offered(List<Group> groups, List<NotOffered> notOffered) {

        public Offered {
            groups = List.copyOf(groups);
            notOffered = List.copyOf(notOffered);
        }
    }

    /**
     * Where a row that comes one way may sit, and what a run that came it would be seen to do, or
     * null where the way places at no class.
     *
     * <p>The same lookup a group's way in goes through, asked of one way on its own. A way in to an
     * arm and the reach of a meeting are the same kind of thing — decisions that hold on the way
     * somewhere — so what they leave open is read here once and not twice.
     *
     * <p>Null where any condition of the way narrows nothing, for the reason a group is dropped for
     * it: what a cell is for is steering a row along the way, and a condition with no classes to
     * put a row at leaves the row free to go the other way round that fork. Offered anyway, it would
     * be a row for an arm it may never take.
     */
    public static CellSelection at(souther.compiler.reading.WayIn way,
                                   souther.compiler.coverage.ControlClaim arrivesAt,
                                   MeasuredInput.MeasuredAxes axes) {
        if (way.decisions().isEmpty()) {
            // Nothing has to hold to get here, so there is nothing to steer a row by. The body
            // itself is reached this way.
            return null;
        }
        Placed placed = placedBy(way.decisions(), axes);
        // One cell and exact, which is what a row is steered to an arm by: a way with a decision the
        // classes do not state leaves the row free to go the other way round that fork.
        if (placed == null || !placed.steering().exact()
                || placed.steering().cells().size() != 1) {
            return null;
        }
        // What a run that arrived would be seen doing, beside what holds on the way. Asked for
        // rather than read off the way, because the two are one thing only where the last decision
        // on the way is the place itself: a `match` names the case a run matched at, which is the
        // arm, while a fork on a comparison names the comparison and leaves the arm unsaid. Held to
        // the way alone, a row seen making the comparison and never seen at the arm certified the
        // arm (issue #1009).
        List<souther.compiler.coverage.ControlClaim> claims = new ArrayList<>(placed.claims());
        if (!claims.contains(arrivesAt)) {
            claims.add(arrivesAt);
        }
        return new CellSelection(placed.steering().cells().getFirst(), claims);
    }

    /**
     * The classes a row arriving by one of {@code ways} sits in, one cell per way this can place.
     * Each way is the conditions that hold on it together.
     *
     * <p>The reading a cell is made by and nothing beside it. A condition places at the classes it
     * leaves whole — a case at the class that is that case, a comparison at every class on its side
     * of a line the axis is cut at — so a row in a cell placed here is a row that comes that way,
     * and not only one that may.
     *
     * <p>A way with a condition placed at no class is left out rather than read wider. What it
     * leaves is a set of rows this cannot name, and a cell drawn without it would take in rows that
     * go the other way round that fork.
     */
    public static List<Cell> whereEach(List<List<souther.compiler.reading.Condition>> ways,
                                       MeasuredInput.MeasuredAxes axes) {
        List<Cell> out = new ArrayList<>();
        for (List<souther.compiler.reading.Condition> way : ways) {
            Cell placed = narrowedBy(way, axes);
            if (placed != null) {
                out.add(placed);
            }
        }
        return out;
    }

    /**
     * Every row that arrives by one of {@code ways}, and maybe more: the rows something asks for,
     * drawn wide.
     *
     * <p>The other direction from {@link #whereEach}. A condition placed at no class is left out of
     * its way rather than the way out of the region, which can only take in rows that do not come
     * that way — so a row that does is in here whatever this could not place. A way whose placed
     * conditions leave a position nothing is one no row comes, and adds no row.
     */
    public static RowRegion holdingEvery(List<List<souther.compiler.reading.Condition>> ways,
                                         MeasuredInput.MeasuredAxes axes) {
        List<RowRegion.Cell> out = new ArrayList<>();
        for (List<souther.compiler.reading.Condition> way : ways) {
            Cell cell = Cell.anything(axes.axes());
            for (souther.compiler.reading.Condition each : way) {
                Cell said = admittedBy(each, axes);
                if (said != null) {
                    cell = cell.and(said);
                    if (cell == null) {
                        break;
                    }
                }
            }
            if (cell != null) {
                out.add(RowRegion.Cell.of(cell, axes.axes()));
            }
        }
        return RowRegion.of(out);
    }

    /**
     * Every row that reaches what {@code way} leads to, and maybe more.
     *
     * <p>Drawn wide, for the reason {@link #holdingEvery} is: what a rule or a point of a line asks
     * for is in here whatever this could not place. A condition no row brings out the way the walk
     * went is a way no row takes, and that is said as no row rather than left out. A narrowing of a
     * position an axis measures keeps the classes it does not tell apart from the cases it leaves,
     * and leaves out only a class that selects another case: a value is one case. Everything else on
     * the way — what the arithmetic took in, and what was declined — narrows nothing here.
     */
    public static RowRegion holdingEveryRowOf(WayToTheBorder way, MeasuredInput.MeasuredAxes axes) {
        if (way.neverComesOut().isPresent()) {
            return RowRegion.NONE;
        }
        List<Axis> measured = axes.axes();
        Cell cell = Cell.anything(measured);
        for (OnTheWay each : way.onTheWay()) {
            if (!(each instanceof OnTheWay.Narrowed narrowed) || !narrowed.crossings().isEmpty()) {
                continue;
            }
            TermPath at = narrowed.position().narrowedFrom().position();
            List<Refinement> left = narrowed.position().narrowing().atoms();
            for (int axis : caseAxesAt(measured, at)) {
                cell = cell.and(onlyTheCases(measured, axis, left));
                if (cell == null) {
                    return RowRegion.NONE;
                }
            }
        }
        return RowRegion.of(List.of(RowRegion.Cell.of(cell, measured)));
    }

    /** The groups worth offering, over the ordered {@code axes}, and the ones held back. */
    public static Offered of(List<Interaction> groups, MeasuredInput.MeasuredAxes axes,
                             int mostCellsPerGroup) {
        List<Group> out = new ArrayList<>();
        List<NotOffered> held = new ArrayList<>();
        for (Interaction group : groups) {
            // A group with no cell is one whose decisions leave no row anywhere, which is no path
            // and nothing owed. One the classes cannot narrow is offered over a wider region.
            Placed reach = group.reachStated() ? placedBy(group.reach(), axes)
                    : new Placed(Steering.unsaid(axes.axes()), List.of(), List.of());
            List<List<Placed>> placed = reach == null ? null : factorsOf(group, axes);
            if (placed == null) {
                continue;
            }
            // Past the limit, and said so rather than dropped. What this costs is the combinations
            // of one group going untried; what saying nothing cost is an arm among them reading as
            // one the body never reaches.
            if (productOf(placed, mostCellsPerGroup) > mostCellsPerGroup) {
                held.add(new NotOffered(claimsOf(reach, placed), settlesOf(reach, placed),
                        WorkFigure.COMBINATIONS_OF_A_GROUP_MEASURED.at(mostCellsPerGroup)));
                continue;
            }
            Group built = new Group(reach, placed);
            if (built.hasACombination()) {
                out.add(built);
            }
        }
        return new Offered(out, held);
    }

    /**
     * Every condition a combination of this group could settle a value by.
     *
     * <p>The union over the way in and every outcome of every factor, which is the same pass
     * {@link #claimsOf} makes and is not the product this declined to walk. A superset, and that is
     * what it is for: a requirement whose conditions are not all in here is one this group cannot
     * state, whichever of its combinations went unwalked. So a reader holding a requirement can
     * tell the groups that might have stated it from the ones that certainly could not, without
     * enumerating anything the limit refused.
     */
    private static java.util.Set<souther.compiler.reading.Condition> settlesOf(
            Placed reach, List<List<Placed>> byFactor) {
        java.util.LinkedHashSet<souther.compiler.reading.Condition> out =
                new java.util.LinkedHashSet<>(reach.settles());
        for (List<Placed> factor : byFactor) {
            for (Placed outcome : factor) {
                out.addAll(outcome.settles());
            }
        }
        return java.util.Collections.unmodifiableSet(out);
    }

    /** Every control point any combination of this group could claim, which is the union over the
     *  way in and every outcome of every factor. One pass, and never the product. */
    private static List<souther.compiler.coverage.ControlClaim> claimsOf(
            Placed reach, List<List<Placed>> byFactor) {
        java.util.LinkedHashSet<souther.compiler.coverage.ControlClaim> out =
                new java.util.LinkedHashSet<>(reach.claims());
        for (List<Placed> factor : byFactor) {
            for (Placed outcome : factor) {
                out.addAll(outcome.claims());
            }
        }
        return List.copyOf(out);
    }

    /**
     * How far the product runs, stopping once it is past anything that would be offered.
     *
     * <p>Stopped rather than run to the end, because a body of enough factors multiplies past what a
     * {@code long} holds and the answer this is asked for is only whether the limit was passed. One
     * over the limit is as good an answer as the true product for that, and is the largest number
     * this ever returns.
     */
    private static long productOf(List<List<Placed>> placed, int mostCells) {
        long size = 1;
        for (List<Placed> factor : placed) {
            size *= factor.size();
            if (size > mostCells) {
                return mostCells + 1L;
            }
        }
        return size;
    }

    /** What each outcome of each factor leaves open, or null where the group is not one to offer. */
    private static List<List<Placed>> factorsOf(Interaction group,
                                                MeasuredInput.MeasuredAxes axes) {
        List<List<Placed>> out = new ArrayList<>();
        for (Factor factor : group.factors()) {
            List<Placed> outcomes = new ArrayList<>();
            for (Outcome outcome : factor.outcomes()) {
                Placed at = placedBy(outcome.holds(), axes);
                if (at == null) {
                    return null;
                }
                outcomes.add(at);
            }
            out.add(outcomes);
        }
        return out;
    }

    /**
     * What {@code made} leaves open and what a run that made it would be seen to have done, or null
     * where any of it narrows nothing or narrows it away.
     *
     * <p>One walk over the decisions for both halves. The classes are this reader's own reading of
     * what the decisions take of the inputs; the claims are carried through untouched, being the
     * reading that owns them. Which decisions are here is decided once, so the claims cannot end up
     * being of a different set of them than the classes are.
     */
    private static Placed placedBy(List<Decision> made, MeasuredInput.MeasuredAxes axes) {
        Steering steering = Steering.exactly(Cell.anything(axes.axes()));
        for (Decision each : made) {
            steering = steering.and(steeringOf(each.constrains(), axes));
            if (steering.impossible()) {
                return null;
            }
        }
        return new Placed(steering, made.stream().map(Decision::claims).toList(),
                made.stream().map(Decision::constrains).toList());
    }

    /**
     * Where a row that makes {@code condition} hold may be looked for.
     *
     * <p>Exact where the classes state it. A condition about a name the cases share is a cell under
     * each case, which is what the row has to be for the name to stand there beside what the
     * condition leaves of its position. Anything the classes do not state is every row, said not to
     * be exact: no position a class of this run divides is what it is about.
     */
    static Steering steeringOf(souther.compiler.reading.Condition condition,
                               MeasuredInput.MeasuredAxes axes) {
        // An arm a run is seen at whichever way it came is the ways it came by: a union of what
        // each way needs, and exact where every way is.
        if (condition instanceof souther.compiler.reading.Condition.Arm arm
                && !arm.comesOutBy().isEmpty()) {
            List<Steering> ways = new ArrayList<>();
            for (List<souther.compiler.reading.Condition> way : arm.comesOutBy()) {
                Steering both = Steering.exactly(Cell.anything(axes.axes()));
                for (souther.compiler.reading.Condition each : way) {
                    both = both.and(steeringOf(each, axes));
                }
                ways.add(both);
            }
            return Steering.union(ways);
        }
        return switch (ConditionPlacement.of(condition, axes)) {
            case ConditionPlacement.AtAPosition(int axis) -> {
                Cell said = admittedAt(condition, axes.axes(), axis, standingOf(condition));
                yield said == null ? Steering.unsaid(axes.axes()) : Steering.exactly(said);
            }
            case ConditionPlacement.UnderTheCases under -> underTheCases(condition, under, axes);
            case ConditionPlacement.AtNoPosition _, ConditionPlacement.Unnamed _ ->
                    Steering.unsaid(axes.axes());
        };
    }

    private static Steering underTheCases(souther.compiler.reading.Condition condition,
                                          ConditionPlacement.UnderTheCases under,
                                          MeasuredInput.MeasuredAxes axes) {
        List<Steering> eachCase = new ArrayList<>();
        for (ConditionPlacement.UnderACase each : under.underEach()) {
            Steering taken = takenBy(each.taken(), axes.axes());
            Cell said = each.measured()
                    ? admittedAt(condition, axes.axes(), each.axis(), each.at()) : null;
            eachCase.add(taken.and(said == null ? Steering.unsaid(axes.axes())
                    : Steering.exactly(said)));
        }
        return Steering.union(eachCase);
    }

    /**
     * What a row has to be for a name to stand where a case puts it, as the cases of the sums it
     * turns on. Not exact where a requirement is of a position no axis measures the value of.
     */
    private static Steering takenBy(Requirements taken, List<Axis> axes) {
        Cell cell = Cell.anything(axes);
        boolean exact = taken.crossings().isEmpty();
        for (var each : taken.refinements().entrySet()) {
            List<Integer> measuring = caseAxesAt(axes, each.getKey());
            exact &= !measuring.isEmpty();
            for (int axis : measuring) {
                cell = cell.and(onlyTheCases(axes, axis, each.getValue().atoms()));
                if (cell == null) {
                    return new Steering(List.of(), true);
                }
            }
        }
        return new Steering(List.of(cell), exact);
    }

    /** The axes that measure which case of its sum the value at {@code at} is. */
    private static List<Integer> caseAxesAt(List<Axis> axes, TermPath at) {
        List<Integer> out = new ArrayList<>();
        for (int i = 0; i < axes.size(); i++) {
            if (axes.get(i).term() instanceof NumericTerm.ValueOf && axes.get(i).path().equals(at)) {
                out.add(i);
            }
        }
        return out;
    }

    /** Every position open, and the one {@code axis} measures the classes that select one of the
     *  cases {@code left} or select none. */
    private static Cell onlyTheCases(List<Axis> axes, int axis, List<Refinement> left) {
        Cell cell = Cell.anything(axes);
        List<PartitionClass> classes = axes.get(axis).classes();
        for (int c = 0; c < classes.size(); c++) {
            Refinement selects = classes.get(c).selects();
            cell.allowed()[axis][c] = selects == null || left.contains(selects);
        }
        return cell;
    }

    /** What {@code holds} leaves open, or null where any of it narrows nothing or narrows it away. */
    private static Cell narrowedBy(List<souther.compiler.reading.Condition> holds,
                                   MeasuredInput.MeasuredAxes axes) {
        Cell cell = Cell.anything(axes.axes());
        for (souther.compiler.reading.Condition each : holds) {
            Cell said = admittedBy(each, axes);
            if (said == null) {
                return null;
            }
            cell = cell.and(said);
            if (cell == null) {
                return null;
            }
        }
        return cell;
    }

    /**
     * Which classes {@code condition} leaves its position, or null where it names none.
     *
     * <p>Where the condition stands is {@link ConditionPlacement}'s answer, which is the one a
     * body's distinctions are read from as well ({@link BodyDistinction}); what it leaves there is
     * {@link #admittedAt}'s. So a cell and that answer cannot read one condition two ways.
     *
     * <p>A condition under the cases is no cell. A cell leaves each position a set of its classes
     * and a row stands at every position it narrows; a condition about a name the cases share
     * leaves one position a set under one case and another under the next, which is a choice
     * between cells and no one of them. Declined here, as a condition that narrows nothing is,
     * rather than read as one of the cases.
     */
    static Cell admittedBy(souther.compiler.reading.Condition condition,
                           MeasuredInput.MeasuredAxes axes) {
        return switch (ConditionPlacement.of(condition, axes)) {
            case ConditionPlacement.AtAPosition(int axis) ->
                    admittedAt(condition, axes.axes(), axis, standingOf(condition));
            case ConditionPlacement.UnderTheCases _, ConditionPlacement.AtNoPosition _,
                 ConditionPlacement.Unnamed _ -> null;
        };
    }

    /** Where {@code condition} is written, for a case of the value there; null for anything
     *  else. */
    static TermPath standingOf(souther.compiler.reading.Condition condition) {
        return condition instanceof souther.compiler.reading.Condition.Case one ? one.at() : null;
    }

    /**
     * Which classes {@code condition} leaves the position {@code axis} measures, or null where it
     * names none of them.
     *
     * <p>The one reading of a condition into classes, once where it stands is known.
     *
     * @param standing where a case of a value is asked, which is the position the axis measures or
     *                 one it is a name worn over; nothing for a comparison, whose number says which
     *                 axis it is
     */
    static Cell admittedAt(souther.compiler.reading.Condition condition, List<Axis> axes,
                           int axis, TermPath standing) {
        switch (condition) {
            case souther.compiler.reading.Condition.Case one -> {
                // Every case the arm answers for. Where the axis is the union itself, its classes
                // are the cases a value there can be, so a case the arm names and the axis has no
                // class of is one the rules refuse there: no value is it, and it admits nothing.
                // Anywhere else a case with no class is something about the position no class of
                // this axis reads, and the condition places at none of them.
                List<PartitionClass> classes = axes.get(axis).classes();
                boolean ofTheUnion = axes.get(axis).path().equals(standing) && !classes.isEmpty()
                        && classes.stream()
                                .allMatch(each -> each.selects() instanceof Refinement.SumCase);
                Cell cell = Cell.anything(axes);
                Arrays.fill(cell.allowed()[axis], false);
                for (String name : one.names()) {
                    int at = -1;
                    for (int c = 0; c < classes.size(); c++) {
                        if (classes.get(c).label().equals(name)) {
                            at = c;
                            break;
                        }
                    }
                    if (at >= 0) {
                        cell.allowed()[axis][at] = true;
                    } else if (!ofTheUnion) {
                        return null;
                    }
                }
                return cell;
            }
            case souther.compiler.reading.Condition.Side one -> {
                // Which construct of the model the decision was about, since a rule is stated at
                // one and the decision was recorded at whichever materialisation of it ran. Empty
                // where the model states nothing there — a comparison inside one of the language's
                // own operations — and no rule draws a line on such a place, so there is no cut of
                // this axis it could be the reading of.
                ModelOccurrence states =
                        ModelOccurrence.statedAt(one.statedAt()).orElse(null);
                if (states == null) {
                    return null;
                }
                boolean onAVisit = one.visit().isPresent();
                Cut line = cutAt(axes.get(axis), states, onAVisit);
                return line == null ? null
                        : sideOf(axes, axis, line, guardOf(line, states, onAVisit), one.held());
            }
            // A fork this reading could not name a position for narrows nothing.
            case souther.compiler.reading.Condition.Arm _ -> {
                return null;
            }
        }
    }

    /** Everything open, and {@code axis} every class but {@code but}. */
    private static Cell allBut(List<Axis> axes, int axis, int but) {
        Cell cell = Cell.anything(axes);
        cell.allowed()[axis][but] = false;
        return cell;
    }

    /** Everything open but {@code axis}, which is left the classes from {@code from} to {@code to}. */
    private static Cell only(List<Axis> axes, int axis, int from, int to) {
        Cell cell = Cell.anything(axes);
        Arrays.fill(cell.allowed()[axis], false);
        for (int c = from; c <= to; c++) {
            cell.allowed()[axis][c] = true;
        }
        return cell;
    }

    /**
     * Which position one decision is about, or -1 where this run measures none — for a condition
     * that stands at one position ({@link ConditionPlacement}).
     *
     * <p>The one lookup, so that what a condition narrows and what it is about are the same
     * question asked once. A second walk written beside it would answer for a position the
     * narrowing never reached.
     */
    static int positionOf(souther.compiler.reading.Condition condition, List<Axis> axes) {
        return switch (condition) {
            case souther.compiler.reading.Condition.Case one -> axisAt(axes, one.at());
            case souther.compiler.reading.Condition.Side one -> axisOf(axes, one.at());
            // A fork this reading could not name a position for is about none of them.
            case souther.compiler.reading.Condition.Arm _ -> -1;
        };
    }

    /**
     * The axis measuring {@code term}, or -1 where none does.
     *
     * <p>The number and never the path it is read from. A location may be measured at more than one
     * number — which hour of a time it is and which minute — and those are one path: asked by path,
     * a comparison about the second of them is answered by the first's axis, which carries no cut of
     * that comparison and so narrows nothing, with nothing saying the condition went unread.
     *
     * <p>Exact and not the nearest. The reading that named this condition and the reading that made
     * the axis ask {@link souther.compiler.inputs.InputNumber} for the number, so a name worn over
     * a type is already looked through on both sides and there is nothing left for a match to be
     * lenient about.
     */
    private static int axisOf(List<Axis> axes, souther.compiler.inputs.NumericTerm term) {
        for (int i = 0; i < axes.size(); i++) {
            if (axes.get(i).term().equals(term)) {
                return i;
            }
        }
        return -1;
    }

    /**
     * Which position the condition is about, allowing for the names a value is written under.
     *
     * <p>{@code total.value} and {@code total} are one position where {@code Total} is a name worn
     * over an {@code Int}: the body reads through the name and the partition divides the position
     * the name is at. The longest match wins, so a record whose own field is divided keeps its own
     * axis rather than being answered by the record's.
     *
     * <p>For a case of a union, which is about the location and not about a number of it. What a
     * comparison is about is {@link #axisOf}'s, exactly.
     */
    private static int axisAt(List<Axis> axes, TermPath path) {
        int found = -1;
        int deepest = -1;
        for (int i = 0; i < axes.size(); i++) {
            TermPath at = axes.get(i).path();
            if (!at.head().equals(path.head()) || at.steps().size() > path.steps().size()) {
                continue;
            }
            if (path.steps().subList(0, at.steps().size()).equals(at.steps())
                    && at.steps().size() > deepest) {
                deepest = at.steps().size();
                found = i;
            }
        }
        return found;
    }

    /**
     * Which classes a comparison coming out {@code held} leaves, by the line {@code guard} drew at
     * {@code line}, or null where the line names no classes.
     */
    static Cell sideOf(List<Axis> axes, int axis, Cut line,
                               LineOrigin.ComparisonOrigin guard, boolean held) {
        int home = holding(axes.get(axis), line);
        if (home < 0) {
            return null;
        }
        // A rule that names one value has no side its values are true on: what it
        // distinguishes is that value from every other. So the cell is the value's own
        // class, or every class but that one — the value where the rule is wanted to hold
        // at it, which an equality held and an inequality broken both are.
        //
        // Only where the class says it is that one value and nothing else. A class holding
        // it among others is one the rule cuts through, and no set of classes is what the
        // rule admits.
        if (guard.facts().claim() instanceof ComparisonClaim.Singled named) {
            if (!axes.get(axis).classes().get(home).holdsOnlyTheNumberAt(line.at())) {
                return null;
            }
            return named.holdsAtTheValue() == held
                    ? only(axes, axis, home, home) : allBut(axes, axis, home);
        }
        // Which side the comparison is true on, from the two facts the order carries: which
        // side of it the cut value itself sits on, and whether the comparison holds there.
        // The whole side and not its nearest class: the comparison admits every value out
        // that way, and a reading that answered with one of them would have said more than
        // the rule does — which is what makes two of them impossible to take together.
        if (!(guard.facts().claim() instanceof ComparisonClaim.Cut order)) {
            return null;
        }
        boolean wantedIsHomeSide = order.holdsAtTheValue() == held;
        // The side the cell wants: the one the rule is satisfied on where it wants the rule
        // met, and the other where it wants it broken.
        boolean wantedIsUp = (held ? order.satisfyingSide()
                : order.satisfyingSide().opposite()) == Towards.ABOVE;
        int last = axes.get(axis).classes().size() - 1;
        int edge = wantedIsHomeSide ? home : (wantedIsUp ? home + 1 : home - 1);
        if (edge < 0 || edge > last) {
            return null;
        }
        return wantedIsUp ? only(axes, axis, edge, last) : only(axes, axis, 0, edge);
    }

    /** The cut the rule stated at {@code states} drew, or null where it drew none. */
    private static Cut cutAt(Axis axis, ModelOccurrence states, boolean onAVisit) {
        for (Cut each : axis.cuts()) {
            if (guardOf(each, states, onAVisit) != null) {
                return each;
            }
        }
        return null;
    }

    /**
     * Which rule of the cut the one stated at {@code states} is, where which way it comes out is
     * which side of the cut a value is.
     *
     * <p>Not a line of a statement of several. Which way {@code Int.max(a, b) > 5} came out says
     * nothing about which side of {@code a = 5} the row was on, since {@code b} may have settled
     * it — so such a line names no class, and the condition narrows nothing here.
     *
     * <p>A decision about one visit to a comparison is about one application of it, and the line of
     * the number that application compares is its own: a comparison applied to each element states
     * a line per element, and which way the comparison came out on that application is which
     * side of that application's line the row is on.
     */
    private static LineOrigin.ComparisonOrigin guardOf(Cut cut, ModelOccurrence states,
                                                       boolean onAVisit) {
        for (LineOrigin origin : cut.origins()) {
            if (origin instanceof LineOrigin.ComparisonOrigin guard
                    && (onAVisit ? guard.decidesItsApplication() : guard.comesOutBySides())
                    && guard.read().states().equals(states)) {
                return guard;
            }
        }
        return null;
    }

    /**
     * Which class of the axis holds the number the line is drawn at, or -1 where none does.
     *
     * <p>Asked with the place the line is at, on the order of the number the axis measures. The
     * classes of that axis are classes of that number, so the two meet as they stand — asked with a
     * value of the position instead, a class about something taken of it is handed the taken number
     * where it expects what stands there, and every class says no.
     */
    private static int holding(Axis axis, Cut line) {
        List<PartitionClass> classes = axis.classes();
        for (int c = 0; c < classes.size(); c++) {
            if (classes.get(c).holdsTheNumberAt(line.at())) {
                return c;
            }
        }
        return -1;
    }
}
