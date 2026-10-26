package souther.compiler.partition;

import souther.compiler.coverage.ControlClaim;
import souther.compiler.reading.CoverageRead;
import souther.compiler.reading.Interaction;
import souther.compiler.reading.WhyNotJoined;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.SequencedMap;

/**
 * What the rows of one behavior are asked for by the decisions its body settles a value with.
 *
 * <p>One requirement per combination the body has a path to: the way in to a meeting, and one
 * outcome of each factor at it. What a criterion asks for is that something was seen doing each of
 * them, and never that a row was written for each — one run settles as many of these as it settles.
 *
 * <p>Told apart by the decisions and held to the claims, which are two readings of one walk and are
 * kept as such. Two combinations that come to the same decisions are one requirement, and they can
 * still be recorded at different places in a body the compiler instrumented twice over — so what
 * answers a requirement is a run that did all of some one of its ways, rather than one that did all
 * the claims of all of them. Written as a union, a requirement two groups arrive at would ask for a
 * run through both.
 *
 * <p>And each way keeps the rows that stand at it beside what a run there does. The two are one
 * reading of one walk, and a reader asking which rows a requirement is about — whether every one of
 * them reaches an {@code unreachable} — asks them of the cell this placed rather than placing the
 * decisions again.
 *
 * <p>And the meetings this asks nothing of though they were read: the ones the limit kept back
 * ({@code notMeasured}), which a wider run walks, and the ones the classes do not place
 * ({@code notPlaced}), which none does. And the sums of kept elements whose decisions could not be
 * joined to the evaluations a run records, which have no group to hold back and are counted
 * ({@code notJoined}); why each was not is the reading's ({@link CoverageRead.Read#notJoined}) and
 * is not a part of what is asked of the rows. None is a meeting with nothing owed at it, and all
 * are said where what this asks for is measured.
 */
public record InteractionRequirements(
        int read,
        SequencedMap<ObligationIdentity.OfACombinationOfDecisions, List<Way>> ways,
        List<OfferedGroup> groups,
        List<InteractionCells.NotOffered> notMeasured,
        List<InteractionCells.NotPlaced> notPlaced,
        int notJoined) {

    /**
     * One outcome of a factor, or the way in to the group, as what a run that took it is seen
     * doing and the decisions it settles.
     *
     * <p>The classes the outcome leaves open are not here: they steer a search and say nothing of
     * what a choice is, and a value that holds them is one an answer cannot be compared by.
     */
    public record Outcome(List<ControlClaim> claims,
                          List<souther.compiler.reading.Condition> settles) {

        public Outcome {
            claims = List.copyOf(claims);
            settles = List.copyOf(settles);
        }

        static Outcome of(InteractionCells.Placed placed) {
            return new Outcome(placed.claims(), placed.settles());
        }
    }

    /**
     * One group of the body's decisions and the requirement each of its choices states.
     *
     * <p>Kept beside {@code ways} because the group is the structure the requirements were counted
     * off: a reader that says which requirements are missing as a set of choices, and not one by
     * one, needs the factors the choices are made of.
     *
     * @param reach    what every choice of the group is under
     * @param byFactor the outcomes of each factor, in the order the group takes them
     * @param at       the requirement of the {@code index}th choice of the group, the first factor
     *                 varying fastest, or null where the factors it takes leave a position nothing
     *                 and the choice is no combination
     */
    public record OfferedGroup(Outcome reach, List<List<Outcome>> byFactor,
                               List<ObligationIdentity.OfACombinationOfDecisions> at) {

        public OfferedGroup {
            Objects.requireNonNull(reach, "a group of decisions has a way in");
            byFactor = byFactor.stream().map(List::copyOf).toList();
            at = Collections.unmodifiableList(new ArrayList<>(at));
            int choices = 1;
            for (List<Outcome> factor : byFactor) {
                choices *= factor.size();
            }
            if (at.size() != choices) {
                throw new IllegalArgumentException("a group of " + choices
                        + " choices states " + at.size() + " requirements");
            }
        }

        /** How many outcomes each factor has, in the order the group takes them. */
        public List<Integer> widths() {
            return byFactor.stream().map(List::size).toList();
        }
    }

    /**
     * One way to a requirement: the rows that take it, and what a run that took it is seen doing.
     *
     * @param where  the rows the cell of the way holds, which are the rows that come this way
     * @param claims what a run that came this way did, all of which a run meeting it does
     */
    public record Way(RowRegion where, List<ControlClaim> claims) {

        public Way {
            Objects.requireNonNull(where, "a way is taken by some rows or none");
            claims = List.copyOf(claims);
        }
    }

    /**
     * The rows that meet {@code item} by some way, which is the rows it asks for: none for a
     * requirement this states no way to.
     */
    public RowRegion rowsOf(ObligationIdentity.OfACombinationOfDecisions item) {
        RowRegion rows = RowRegion.NONE;
        for (Way way : ways.getOrDefault(item, List.of())) {
            rows = rows.or(way.where());
        }
        return rows;
    }

    public InteractionRequirements {
        ways = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(ways));
        groups = List.copyOf(groups);
        notMeasured = List.copyOf(notMeasured);
        notPlaced = List.copyOf(notPlaced);
        if (read < 0 || notJoined < 0) {
            throw new IllegalArgumentException("meetings are counted from none: " + read
                    + " read, " + notJoined + " not joined");
        }
        int heldBack = notMeasured.size() + notPlaced.size() + notJoined;
        if (read < heldBack) {
            throw new IllegalArgumentException("more meetings were held back than were read: "
                    + heldBack + " of " + read);
        }
    }

    /** Nothing asked of a behavior whose decisions meet nowhere, which is not a group of none. */
    public static final InteractionRequirements NONE =
            new InteractionRequirements(0, new LinkedHashMap<>(), List.of(), List.of(), List.of(),
                    0);

    /**
     * Whether the body has meetings at all, which is what says the criterion this behavior is held
     * to is the interactions.
     *
     * <p>Read off what the walk found and never off what came of it. A meeting whose combinations
     * the classes could not place, and one the measure would not walk, are meetings — and a
     * behavior falling back to the pair space because a measurement went short is the criterion
     * moving with how the measuring went, which is what the fallback must never be.
     */
    public boolean any() {
        return read > 0;
    }

    /**
     * The requirements the meetings of one behavior state, in the order the walk met them.
     *
     * <p>The combinations are counted off the groups the cells reader offers, so a choice whose
     * factors leave a position nothing is left out here as it is there: the body has no path to it,
     * and what has no path is not something to ask for. Which is the one thing the classes decide
     * about a requirement — whether it exists — and they decide nothing about whether it is met.
     */
    public static InteractionRequirements of(String behavior, List<Interaction> groups,
                                             List<WhyNotJoined> notJoined,
                                             MeasuredInput.MeasuredAxes axes,
                                             int mostCellsPerGroup) {
        InteractionCells.Offered offered = InteractionCells.of(groups, axes, mostCellsPerGroup);
        SequencedMap<ObligationIdentity.OfACombinationOfDecisions, List<Way>> ways =
                new LinkedHashMap<>();
        List<OfferedGroup> kept = new ArrayList<>();
        // What each decision hashes to, by the decision itself: the choices of a group are taken
        // from the same few outcomes, so a decision is hashed once and not once per choice.
        Map<souther.compiler.reading.Condition, Integer> hashes = new IdentityHashMap<>();
        for (InteractionCells.Group group : offered.groups()) {
            List<ObligationIdentity.OfACombinationOfDecisions> at = new ArrayList<>();
            for (int index = 0; index < group.size(); index++) {
                CellSelection selection = group.at(index);
                if (selection == null) {
                    at.add(null);
                    continue;
                }
                ObligationIdentity.OfACombinationOfDecisions item =
                        new ObligationIdentity.OfACombinationOfDecisions(
                                behavior, DecisionSet.of(group.settledAt(index), hashes));
                at.add(item);
                List<Way> already = ways.computeIfAbsent(item, _ -> new ArrayList<>());
                Way way = new Way(RowRegion.of(List.of(
                        RowRegion.Cell.of(selection.cell(), axes.axes()))), selection.claims());
                if (!already.contains(way)) {
                    already.add(way);
                }
            }
            kept.add(new OfferedGroup(Outcome.of(group.reach()),
                    group.byFactor().stream()
                            .map(factor -> factor.stream().map(Outcome::of).toList()).toList(),
                    at));
        }
        return new InteractionRequirements(groups.size() + notJoined.size(), ways, kept,
                offered.notOffered(), offered.notPlaced(), notJoined.size());
    }

    /**
     * Whether {@code done} did all the claims of some one way of meeting {@code item}.
     *
     * <p>Some one way, because a run makes the decisions where it makes them. Two ways to the same
     * decisions are two places a body records them, and a row that went one of them did what the
     * requirement asks — held to both, a requirement that arose twice would ask for a run that
     * passed through a body twice.
     *
     * <p>False for a requirement this states no way to, which is one of another behavior's.
     */
    public boolean met(ObligationIdentity.OfACombinationOfDecisions item,
                       java.util.function.Predicate<ControlClaim> done) {
        for (Way way : ways.getOrDefault(item, List.of())) {
            if (way.claims().stream().allMatch(done)) {
                return true;
            }
        }
        return false;
    }
}
