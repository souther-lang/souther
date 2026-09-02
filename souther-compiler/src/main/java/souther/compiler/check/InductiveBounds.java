package souther.compiler.check;

import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.Induction;
import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.numeric.LinearForm;

import java.util.Collection;
import java.util.Map;

/**
 * A walk this check reads, put to the proof that a walk stays inside a range.
 *
 * <p>The theorem is {@link Induction}'s and nothing of it is repeated here: what is here is this
 * check's half of it — the forms a walk was named as, the domain they are read against, and the
 * recipes an atom inside a step stands for. The measuring side reads a walk out of a term and a
 * container's element range instead, and puts its own half to the same proof.
 *
 * <p>What arrives is a seed, an accumulator, a step, and facts about what the step is handed, read
 * where the walk was named. Nothing here is a tree to be read again and nothing holds an
 * environment: what could be read of the walk was read then, and a walk whose parts could not be
 * read that way is not one of these at all. So no operation's name reaches this either, and an
 * operation the library gains that reduces the same way is proved unchanged.
 */
final class InductiveBounds {

    private InductiveBounds() {}

    /**
     * A walk, as the numbers it is made of: what it starts from, what the accumulator is called while
     * the step runs, what the step answers, and what holds of everything else the step is handed.
     */
    record Walk(LinearForm<FactSubject> seed, FactSubject accumulator,
                LinearForm<FactSubject> step, StepInputFacts inputs) {}

    /**
     * What a form lies between in a domain, with the arithmetic its atoms stand for read against
     * that same domain.
     *
     * <p>Taken rather than done here, because which recipes an atom has is
     * {@link DerivedNumericFacts}' table and reading it a second way would be a second answer. What this
     * asks of it is the part that matters to a proof: the domain is the one the question is asked
     * in, so a product inside a step is read under the induction hypothesis and not under what was
     * known before it.
     */
    @FunctionalInterface
    interface Reading {

        Bounds of(LinearForm<FactSubject> form, DerivedNumericFacts.ReadingDomain domain);
    }

    /**
     * What {@code walk} answers, as far as {@code base} settles it.
     *
     * <p>{@code base} is the reading the question was asked under and is never written to: every
     * candidate is checked against a domain forked from it, and what comes back is a range and not a
     * domain. So this can be asked twice with two readings and answer twice, and neither answer can
     * reach the other.
     */
    static Bounds provenOf(Walk walk, DerivedNumericFacts.ReadingDomain base, Terms terms,
                           Reading read) {
        return Induction.proves(base,
                given -> new Read(walk, given.taking(walk.inputs()), terms, read));
    }

    /**
     * This check's walk read against one domain.
     *
     * <p>The whole of what the proof is allowed to ask, so the facts a candidate is made from and
     * the facts the step is checked against are the one domain this holds. A domain assumed for the
     * accumulator makes another of these and never reaches back into this one: nothing derived under
     * an assumed accumulator is true where the accumulator is not assumed, which is what
     * {@link DerivedNumericFacts} declines to be and for the same reason.
     */
    private record Read(Walk walk, DerivedNumericFacts.ReadingDomain domain, Terms terms,
                        Reading read) implements Induction.Prepared {

        @Override
        public boolean isBottom() {
            return domain.isBottom();
        }

        @Override
        public Bounds seed() {
            return read.of(walk.seed(), domain);
        }

        @Override
        public Bounds step() {
            return read.of(walk.step(), domain);
        }

        @Override
        public Collection<Bounds> whatTheStepIsHanded() {
            return walk.inputs().at().values();
        }

        @Override
        public Induction.Prepared assuming(Bounds candidate) {
            // The accumulator's own spacing, since a range asserted about an atom whose spacing was
            // never recorded is one the domain refuses.
            Map<FactSubject, Granularity> spacing =
                    terms.kindsOf(LinearForm.atom(walk.accumulator()));
            return new Read(walk, domain.assuming(walk.accumulator(), candidate, spacing),
                    terms, read);
        }
    }
}
