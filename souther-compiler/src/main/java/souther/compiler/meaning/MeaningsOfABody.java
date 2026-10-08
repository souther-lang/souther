package souther.compiler.meaning;

import souther.compiler.types.ModelOccurrence;

import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * What each condition of one body states, filed under the construct of the model it is asked at.
 *
 * <p>Read once, off the representation where the language's operations stand, and looked up by a
 * reader walking the tree that runs: the two trees agree about which construct of the model a node
 * is one of ({@link ModelOccurrence}), and about nothing finer. One construct may be met at more
 * than one place in either tree — a helper's construct is copied wherever the helper is — and where
 * the copies here state different things the site is ambiguous and answers nothing, so no reader
 * takes one copy's statement for another's.
 *
 * @param stated    what is stated at each site read to one statement
 * @param ambiguous the sites whose copies state different things
 */
public record MeaningsOfABody(Map<Site, Proposition> stated, Set<Site> ambiguous) {

    /** A body nothing was read of. */
    public static final MeaningsOfABody NONE = new MeaningsOfABody(Map.of(), Set.of());

    public MeaningsOfABody {
        stated = Map.copyOf(stated);
        ambiguous = Set.copyOf(ambiguous);
    }

    /** Which part of a construct is asked whether it holds. */
    public enum Part {
        /** The condition a fork chooses its arm by. */
        CONDITION,
        /** The left operand of a short-circuit, which decides whether the right one runs. */
        LEFT,
        /** The construct itself, a comparison whose outcome a run records. */
        ITSELF
    }

    /**
     * Where a truth is asked: a construct of the model, and which part of it.
     *
     * @param construct the construct the two readings of the body agree it is
     * @param part      which of its parts is the truth asked
     */
    public record Site(ModelOccurrence construct, Part part) {}

    /** What is stated at {@code site}, or empty where nothing was read there or its copies state
     *  different things. */
    public Optional<Proposition> at(Site site) {
        return ambiguous.contains(site) ? Optional.empty() : Optional.ofNullable(stated.get(site));
    }
}
