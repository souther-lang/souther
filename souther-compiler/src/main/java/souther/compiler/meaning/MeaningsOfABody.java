package souther.compiler.meaning;

import souther.compiler.check.ClauseName;
import souther.compiler.types.ModelOccurrence;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
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

    /**
     * Which part of a construct is asked whether it holds: a truth the construct asks, or an arm of
     * a fork a run enters.
     */
    public sealed interface Part permits Part.Asked, Part.Arm {

        /** A truth a construct asks. */
        enum Asked implements Part {
            /** The condition a fork chooses its arm by. */
            CONDITION,
            /** The left operand of a short-circuit, which decides whether the right one runs. */
            LEFT,
            /** The construct itself, a comparison whose outcome a run records. */
            ITSELF
        }

        /**
         * An arm of a fork, which holds where a run enters it.
         *
         * <p>Named by what the source names it by, so that an arm is the same arm in every copy of
         * the fork and after an edit that moves another: a case of a {@code match} by where it is
         * written among the cases, and an arm of an attempt by the clause of the invariant it
         * answers.
         */
        sealed interface Arm extends Part {}

        /** The arm of a {@code match} written {@code arm}-th among its cases, from nought. */
        record OfACase(int arm) implements Arm {

            public OfACase {
                if (arm < 0) {
                    throw new IllegalArgumentException("a case is written somewhere among the cases");
                }
            }
        }

        /** The arm of an attempt taken where every clause of the invariant held and the value was
         *  built. */
        record Built() implements Arm {}

        /**
         * A departure of an attempt: the one answering the clause named {@code clause} — the first
         * clause not to hold — or, where empty, the one answering every failure no other departure
         * names.
         */
        record Departed(Optional<ClauseName> clause) implements Arm {

            public Departed {
                Objects.requireNonNull(clause, "a departure names a clause or names none");
            }
        }
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
     * <p>Made by concluding the derivation and no other way ({@link Conclusion#meaningOf}), so what
     * is stated is always what the derivation beside it concludes. Two values alike in both are
     * equal.
     */
    public static final class Meaning {

        private final Proposition states;
        private final Derivation how;

        Meaning(Proposition states, Derivation how) {
            this.states = Objects.requireNonNull(states, "a site states something");
            this.how = Objects.requireNonNull(how, "what a site states was derived");
        }

        /** What holds where the truth asked there does. */
        public Proposition states() {
            return states;
        }

        /** The derivation it was concluded from. */
        public Derivation how() {
            return how;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Meaning that && states.equals(that.states)
                    && how.equals(that.how);
        }

        @Override
        public int hashCode() {
            return Objects.hash(states, how);
        }

        @Override
        public String toString() {
            return "Meaning[states=" + states + ", how=" + how + "]";
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

        /**
         * What a closure's body states on each of its applications ({@code each}, one reading of the
         * body per application), met as what each site in it states on the application a run meets
         * it on ({@link Derivation.OnEachApplication}).
         *
         * <p>Not as copies of the site. A copy is the same construct met at another place, and two
         * copies stating different things are a site that says nothing; applications are one place
         * met with one value and then another, and stating different things on each is what such a
         * site does. A site with copies on some application is still a site with copies.
         */
        public void metOnEachApplication(List<MeaningsOfABody> each) {
            Set<Site> sites = new LinkedHashSet<>();
            each.forEach(one -> {
                sites.addAll(one.stated().keySet());
                sites.addAll(one.ambiguous());
            });
            for (Site site : sites) {
                if (each.stream().anyMatch(one -> one.ambiguous().contains(site))) {
                    ambiguous.add(site);
                    continue;
                }
                List<Derivation> how = each.stream().map(one -> one.stated().get(site))
                        .filter(Objects::nonNull).map(Meaning::how).toList();
                met(site, new Conclusion(Optional.of(site.construct()))
                        .meaningOf(new Derivation.OnEachApplication(how)));
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

    /** Why nothing is stated at {@code site}, where {@link #at} answers nothing. */
    public WhyUnread whyNothingAt(Site site) {
        return ambiguous.contains(site) ? new WhyUnread.CopiesStateDifferentThings()
                : new WhyUnread.NotMetByTheReading();
    }
}
