package souther.compiler.partition;

import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * Which candidates a row for a case of a statement is built from: how far below the start of a
 * search a node is looked for, and the places a candidate is written at for it.
 *
 * <p>The plan of a search for a row and no part of what a case means. {@code BELOW_IT} is a node
 * at some depth meeting what the search asks, and that is the same whether it is looked for three
 * levels down or ten ({@link CaseOfAStatement}, {@link Proposition.SomeReachable}). How many
 * levels are tried is the search's, and a case no candidate was found for stays unmeasured: it is
 * never said to be out of reach.
 *
 * @param levelsBelowTheStart how many levels below the start the step that finds one below is
 *                            looked for at, nearest first
 */
public record CaseCandidates(int levelsBelowTheStart) {

    /**
     * How many levels below the start a node is looked for by a search for a row. Not one of the
     * published figures ({@link CompositionBudget}) because a search that comes back without a row
     * reports no figure it stopped at, and a figure nothing reports is one nobody could be told
     * to raise.
     */
    public static final int MOST_LEVELS_BELOW_THE_START = 3;

    /** The candidates the measurement makes ways for: the first level below the start, and only
     *  where its reading read the places ({@link #reads}). */
    public static final CaseCandidates NEARBY = new CaseCandidates(1);

    /** The candidates a search for a row is made with. */
    public static final CaseCandidates OF_THE_SEARCH =
            new CaseCandidates(MOST_LEVELS_BELOW_THE_START);

    public CaseCandidates {
        if (levelsBelowTheStart < 1) {
            throw new IllegalArgumentException("a node is looked for at least one level below");
        }
    }

    /** How many levels {@code which} is asked at: the levels below the start for the step that
     *  finds one below, and the one asking there is for every other step. */
    public int levelsAsked(CaseOfAStatement.Search which) {
        return which.step() == CaseOfAStatement.Step.BELOW_IT ? levelsBelowTheStart : 1;
    }

    /**
     * Whether {@code domain} read a position at {@code place}.
     *
     * <p>The one question a way to a case asks of a reading before it is made. A place whose rules
     * some value names is not a place the reading worked out: the element of a container on the
     * edge of a recursive type is named by its own rules and has no position, so what a row may be
     * there is not something the reading can say.
     */
    public static boolean reads(InputDomain domain, TermPath place) {
        return domain.at(place) != null;
    }

    /**
     * The places a candidate is written at for {@code which}, at every level it is asked at: the
     * containers and elements on the way down, each place of the node reached that the statement
     * reads, and every place the reading holds of the start moved to that node. Empty for a step
     * that asks nothing inside the nodes below.
     *
     * <p>A node below is a node as the start is. The places of the start are the places a node has,
     * whatever the statement happens to read of it, and the elements of a container whose elements
     * a number is taken of are among them. Finite whatever the depth the type recurses to, for it
     * is the places of one node at the levels asked.
     *
     * @param measured the reading the measurement was made with
     */
    public List<TermPath> placesToBuildFor(CaseOfAStatement.Search which, InputDomain measured) {
        List<TermPath> out = new ArrayList<>();
        for (int level = 1; level <= levelsAsked(which); level++) {
            Optional<Proposition.SomeReachable.NodeBelowMeeting> below =
                    which.step() == CaseOfAStatement.Step.BELOW_IT
                            ? which.statement().someNodeBelowMeetingIt(level) : Optional.empty();
            below.ifPresent(each -> {
                out.addAll(each.places());
                for (Position position : measured.positions()) {
                    TermPath there =
                            position.path().movedFrom(which.statement().at(), each.reached());
                    if (there != null) {
                        out.add(there);
                    }
                }
            });
        }
        return List.copyOf(out);
    }
}
