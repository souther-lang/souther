package souther.compiler.partition;

import souther.compiler.coverage.ControlClaim;
import souther.compiler.reading.Interaction;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
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
 */
public record InteractionRequirements(
        int read,
        SequencedMap<ObligationIdentity.OfACombinationOfDecisions, List<Way>> ways,
        List<InteractionCells.NotOffered> notMeasured) {

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
        notMeasured = List.copyOf(notMeasured);
        if (read < 0) {
            throw new IllegalArgumentException("meetings are counted from none: " + read);
        }
        if (read < notMeasured.size()) {
            throw new IllegalArgumentException("more meetings were held back than were read: "
                    + notMeasured.size() + " of " + read);
        }
    }

    /** Nothing asked of a behavior whose decisions meet nowhere, which is not a group of none. */
    public static final InteractionRequirements NONE =
            new InteractionRequirements(0, new LinkedHashMap<>(), List.of());

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
                                             MeasuredInput.MeasuredAxes axes,
                                             int mostCellsPerGroup) {
        InteractionCells.Offered offered = InteractionCells.of(groups, axes, mostCellsPerGroup);
        SequencedMap<ObligationIdentity.OfACombinationOfDecisions, List<Way>> ways =
                new LinkedHashMap<>();
        for (InteractionCells.Group group : offered.groups()) {
            for (int index = 0; index < group.size(); index++) {
                CellSelection selection = group.at(index);
                if (selection == null) {
                    continue;
                }
                ObligationIdentity.OfACombinationOfDecisions item =
                        new ObligationIdentity.OfACombinationOfDecisions(
                                behavior, group.settledAt(index));
                List<Way> already = ways.computeIfAbsent(item, _ -> new ArrayList<>());
                Way way = new Way(RowRegion.of(List.of(
                        RowRegion.Cell.of(selection.cell(), axes.axes()))), selection.claims());
                if (!already.contains(way)) {
                    already.add(way);
                }
            }
        }
        return new InteractionRequirements(groups.size(), ways, offered.notOffered());
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
