package souther.compiler.check;

import souther.compiler.numeric.NumericDomain.LinearForm;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Everything this check knows about one atom by knowing which value it is.
 *
 * <p>One record and not a table per kind of thing that could be known. What was recorded about an
 * atom used to be two maps read by name — how it was computed, and which walk it was the answer of
 * — and a reader wanting either asked both by name. Two costs, and the second is the one that bites:
 * a third thing worth knowing arrives as a third map, every reader that enumerates them is a reader
 * somebody has to remember to visit, and the one that is not visited answers as though the atom
 * carried nothing. That is what left a size inside a reduction's step unbounded (#988).
 *
 * <p>Two things are known, and they are different in kind rather than in where they came from.
 *
 * <p>{@link #computation} is how the value was reached from other values, and what it gives is
 * conditional: what a product lies between is the answer of whatever domain its factors are read in,
 * so it is a recipe to be put through a reading and not a fact.
 *
 * <p>{@link #intrinsic} is what holds of the value whatever any reading says — a size is never
 * negative, an absolute value is not, a filtered container is no longer than what it was filtered
 * from. No path establishes these and no path can take them away, so they are true in every domain
 * this atom is read in and are taken in before any recipe is put through
 * ({@link DerivedNumericFacts#readingOf}).
 *
 * <p>The two graphs these make are not the same graph and their cycles do not mean the same thing.
 * A computation is written over strictly smaller expressions, so an atom reachable from itself
 * through computations is this check having named a value it built out of itself, and
 * {@link DerivedNumericFacts} refuses it. An intrinsic relation names whatever values it relates,
 * with no such ordering: {@code length(filter(xs)) <= length(xs)} and a relation the other way about
 * would be two true statements and not a contradiction. So reachability over both edges together
 * ({@link Terms#reached}) is a closure taken with a visited set and terminates on repetition, while
 * derivation over computation edges alone refuses repetition outright. Neither may be written in
 * terms of the other.
 *
 * @param computation how the value was reached, which may be {@link Computation.None}: a size is a
 *                   value this knows something about and computes nothing from
 * @param intrinsic   what holds of the value whatever it was reached by, as relations. Relations and
 *                    not ranges, because a relation is the same statement in every domain and what
 *                    it comes to is the domain's answer — and because half of these relate this
 *                    value to another one rather than bounding it
 */
record AtomKnowledge(Computation computation, List<NumericConstraint> intrinsic) {

    AtomKnowledge {
        intrinsic = List.copyOf(intrinsic);
    }

    /** An atom nothing has been recorded about yet. */
    static AtomKnowledge nothing() {
        return new AtomKnowledge(Computation.None.INSTANCE, List.of());
    }

    AtomKnowledge computedBy(Computation how) {
        return new AtomKnowledge(how, intrinsic);
    }

    AtomKnowledge carrying(List<NumericConstraint> facts) {
        return new AtomKnowledge(computation, facts);
    }

    /**
     * The atoms reading this one reads directly, which is one edge and not the closure of them.
     *
     * <p>Worked out from what is here rather than recorded beside it. A recorded edge set is a second
     * writing of what the computation and the relations already say, and the day an intrinsic rule is
     * added the second writing is the one nobody updates — which is the same failure this record
     * exists to stop rather than a defence against it.
     *
     * <p>{@code self} is left out. A relation is written over the value it is about, so every
     * intrinsic fact names this atom, and {@code x >= 0} is not {@code x} depending on {@code x}.
     * The closure would terminate either way; what this keeps is the model saying what is true.
     */
    Set<FactSubject> directlyReads(FactSubject self) {
        Set<FactSubject> out = new LinkedHashSet<>();
        for (LinearForm<FactSubject> form : computation.formsRead()) {
            out.addAll(form.coefs().keySet());
        }
        for (NumericConstraint fact : intrinsic) {
            out.addAll(fact.atoms());
        }
        out.remove(self);
        return out;
    }

    /**
     * How a value was reached from other values, where anything reached it.
     *
     * <p>A sum, so that an atom recorded as computed two ways is a state nothing can hold. Held as
     * two tables this was a disagreement each table checked for on its own and neither checked
     * across: a value filed as a walk's answer and as a piece of arithmetic had both recorded and
     * was read as whichever the reader asked for first (#988).
     */
    sealed interface Computation {

        /**
         * The forms reading this computation reads from.
         *
         * <p>Abstract, so a way of reaching a value added later answers for itself. What a recipe is
         * read from is the recipe's own answer already ({@link Derivation#formsRead}) and for the
         * same reason: worked out from which parts happen to be forms, the first one that arrives
         * inside something else is missed quietly.
         */
        List<LinearForm<FactSubject>> formsRead();

        /** Nothing reached it: the value is what it is, and whatever is known of it is intrinsic. */
        record None() implements Computation {

            static final None INSTANCE = new None();

            @Override
            public List<LinearForm<FactSubject>> formsRead() {
                return List.of();
            }
        }

        /** Arithmetic the affine fragment does not carry, as the recipe it is. */
        record Derived(Derivation recipe) implements Computation {

            @Override
            public List<LinearForm<FactSubject>> formsRead() {
                return recipe.formsRead();
            }
        }

        /** What a library operation reached by applying a closure over and over. */
        record Reduction(InductiveBounds.Walk walk) implements Computation {

            @Override
            public List<LinearForm<FactSubject>> formsRead() {
                return List.of(walk.seed(), walk.step());
            }
        }
    }
}
