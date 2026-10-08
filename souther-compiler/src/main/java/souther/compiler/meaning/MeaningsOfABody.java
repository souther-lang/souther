package souther.compiler.meaning;

import souther.compiler.types.ModelOccurrence;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;
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
 * <p>Two copies are compared by what they state and not by how it was derived. Two expansions of
 * one helper can reach one proposition by different rules, and that makes the site no less one
 * statement. How the first was derived is the one kept, and it is part of what this is equal by:
 * a reader explaining a fork from it would otherwise be handed an account a revision ago.
 *
 * @param stated    what is stated at each site read to one statement, and how
 * @param ambiguous the sites whose copies state different things
 */
public record MeaningsOfABody(Map<Site, Meaning> stated, Set<Site> ambiguous) {

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

    /**
     * What a site states, and how that was derived.
     *
     * @param states what holds where the truth asked there does
     * @param how    the derivation it was concluded from
     */
    public record Meaning(Proposition states, Derivation how) {

        public Meaning {
            Objects.requireNonNull(states, "a site states something");
            Objects.requireNonNull(how, "what a site states was derived");
        }
    }

    /**
     * What is stated at each site, filed as copies of it are met.
     *
     * <p>A site met again is compared by what the copy states: the same proposition derived another
     * way is the same statement and leaves the first derivation where it is, and another proposition
     * makes the site ambiguous.
     */
    public static final class Filing {

        private final Map<Site, Meaning> stated = new LinkedHashMap<>();
        private final Set<Site> ambiguous = new HashSet<>();

        /** {@code meaning}, met at {@code site}. */
        public void met(Site site, Meaning meaning) {
            Meaning before = stated.putIfAbsent(site, meaning);
            if (before != null && !before.states().equals(meaning.states())) {
                ambiguous.add(site);
            }
        }

        /** What was filed. */
        public MeaningsOfABody filed() {
            return new MeaningsOfABody(stated, ambiguous);
        }
    }

    /** What is stated at {@code site}, or empty where nothing was read there or its copies state
     *  different things. */
    public Optional<Proposition> at(Site site) {
        return meaningAt(site).map(Meaning::states);
    }

    /** What is stated at {@code site} and how, or empty as {@link #at} is. */
    public Optional<Meaning> meaningAt(Site site) {
        return ambiguous.contains(site) ? Optional.empty() : Optional.ofNullable(stated.get(site));
    }
}
