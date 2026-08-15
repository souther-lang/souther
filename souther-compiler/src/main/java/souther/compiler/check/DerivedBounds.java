package souther.compiler.check;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.Intervals;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What follows about the values arithmetic outside the affine fragment answers.
 *
 * <p>A product of two values and a truncating quotient are not linear, so the domain holds them as
 * atoms and knows nothing of them. What their factors lie between it does know, and that is enough
 * to bound them — so this reads the factors out of a domain, puts the arithmetic through
 * {@link Intervals}, and hands back the domain with what came out taken as holding.
 *
 * <p>A projection and not an inference. Every bound is derived from the domain it was given, once,
 * and the results are taken in together at the end; nothing derived here is read back to derive
 * something else about the same atom. Letting a derived bound feed the next round would be
 * interval reasoning that tightens under its own answers — {@code x <= 0.5} giving
 * {@code x * x <= 0.25} giving a tighter {@code x} again — which is a different thing to build and
 * a different thing to state.
 *
 * <p>The domain is the argument, which is what keeps a derived bound the path's. The check reads a
 * construction twice, under what the guards established and under nothing, and the two get their
 * own answers here because they ask with their own domains.
 */
final class DerivedBounds {

    private DerivedBounds() {}

    /**
     * The atoms whose recipe each reading evaluated, one entry per reading, where a test in this
     * package is watching — and null everywhere else.
     *
     * <p>Beside {@link InvariantChecker#WATCHING} and for a reason of its own. What this states is
     * that a reading does no work the question it was asked cannot reach, and that is not something
     * any diagnostic says: a reading that derived every recipe in the behavior answers exactly what
     * a reading that derived three of them answers. So the property has nowhere else to be read,
     * and one that nothing reads stops being true without anything failing.
     */
    static List<List<Term>> WATCHING;

    /**
     * {@code base} with what follows about the arithmetic outside the affine fragment that this
     * reading can reach, taken as holding.
     *
     * <p>What it can reach is the two together: the atoms the clauses are decided by, and the atoms
     * {@code base} says anything about. Neither alone is it. A clause naming a product needs that
     * product derived though no guard mentions it; and a clause naming no product at all reaches
     * one through a guard that equated the two, since what a bound on the product gives {@code
     * total} it gives through the difference the domain recorded. Everything else {@code terms}
     * named is arithmetic somewhere else in this behavior: {@code terms} is a memo of what the
     * naming has seen, which is a longer-lived thing than the question asked here, and an atom
     * outside both sets is one no question asked of this domain can reach
     * ({@link NumericDomain#atomsSpokenOf}).
     *
     * <p>One pass, and not because the roots happen not to grow. Every derivation reads {@code
     * base} — {@link #derive} is handed it at every level — so what is derived for an atom is a
     * function of {@code base} and the recipes alone. A bound derived here is an answer of this
     * reading and never a premise another recipe is derived from, which is the interval reasoning
     * that tightens under its own answers that this declines to be. So the recipes reachable from
     * the roots are all of them, whatever order they are walked in.
     */
    static NumericDomain<Term> refine(NumericDomain<Term> base, Terms terms, Set<Term> asked) {
        Map<Term, Derivation> recipes = terms.derivations();
        Map<Term, Bounds> derived = new LinkedHashMap<>();
        if (!recipes.isEmpty() && !base.isBottom()) {
            for (Term atom : roots(recipes, base, asked)) {
                derive(atom, base, terms, derived, new LinkedHashSet<>());
            }
        }
        watched(derived.keySet());
        NumericDomain<Term> out = base;
        for (Map.Entry<Term, Bounds> one : derived.entrySet()) {
            out = taking(out, one.getKey(), one.getValue(), terms);
        }
        return out;
    }

    /** The atoms this reading is to derive from: the ones it can reach that were recorded as
     * arithmetic. Walked from the reaching side rather than from {@code recipes}, so what it costs
     * is what the question is about and not how much arithmetic the behavior contains. */
    private static Set<Term> roots(Map<Term, Derivation> recipes, NumericDomain<Term> base,
                                   Set<Term> asked) {
        Set<Term> out = new LinkedHashSet<>();
        for (Term atom : asked) {
            if (recipes.containsKey(atom)) {
                out.add(atom);
            }
        }
        for (Term atom : base.atomsSpokenOf()) {
            if (recipes.containsKey(atom)) {
                out.add(atom);
            }
        }
        return out;
    }

    /** Records the recipes this reading evaluated, where a test is reading them. Every atom here
     * had its recipe put through {@link Intervals}: {@link #derive} answers a second ask from what
     * it remembered, so an atom is written once however many forms name it. */
    private static void watched(Set<Term> evaluated) {
        List<List<Term>> watching = WATCHING;
        if (watching != null) {
            watching.add(List.copyOf(evaluated));
        }
    }

    /**
     * What {@code atom} lies between, computed once and remembered.
     *
     * <p>{@code deriving} holds what this is in the middle of answering. An atom is recorded against
     * arithmetic over the parts it was built from, and a part is a strictly smaller expression, so
     * the recipes make a graph with no way back to where it started; reaching one that is already
     * being answered would mean the naming built an atom out of itself.
     */
    private static Bounds derive(Term atom, NumericDomain<Term> base, Terms terms,
                                 Map<Term, Bounds> done, Set<Term> deriving) {
        Bounds had = done.get(atom);
        if (had != null) {
            return had;
        }
        if (!deriving.add(atom)) {
            throw new AnAtomComputedFromItself(atom);
        }
        Derivation recipe = terms.derivations().get(atom);
        Bounds bounds = switch (recipe) {
            case Derivation.Product product -> Intervals.product(
                    boundsOf(product.left(), base, terms, done, deriving),
                    boundsOf(product.right(), base, terms, done, deriving));
            case Derivation.Quotient quotient -> Intervals.truncatingQuotient(
                    boundsOf(quotient.numerator(), base, terms, done, deriving),
                    quotient.divisor());
        };
        deriving.remove(atom);
        done.put(atom, bounds);
        return bounds;
    }

    /**
     * What {@code form} lies between, with whatever its own atoms were derived to taken in first.
     *
     * <p>A factor may itself be a product — {@code a * b / 100} is one — and what the domain proves
     * about such an atom is nothing at all until the arithmetic under it has been read. Only the
     * atoms this form names are derived, so what is read is the expression's own structure and not
     * everything else the reading has recorded.
     */
    private static Bounds boundsOf(LinearForm<Term> form, NumericDomain<Term> base, Terms terms,
                                   Map<Term, Bounds> done, Set<Term> deriving) {
        NumericDomain<Term> with = base;
        for (Term atom : form.coefs().keySet()) {
            if (terms.derivations().containsKey(atom)) {
                with = taking(with, atom, derive(atom, base, terms, done, deriving), terms);
            }
        }
        return with.boundsOf(form);
    }

    /** {@code d} with {@code atom} taken to lie between {@code bounds}. An end the range does not
     * reach is asserted as the strict comparison it is, which is what the domain reads a range's
     * ends as. */
    private static NumericDomain<Term> taking(NumericDomain<Term> d, Term atom, Bounds bounds,
                                              Terms terms) {
        LinearForm<Term> form = LinearForm.atom(atom);
        Map<Term, Granularity> kinds = terms.kindsOf(form);
        NumericDomain<Term> out = d;
        if (bounds.min() != null) {
            out = out.assume(form.minus(LinearForm.constant(count(bounds.min()))),
                    bounds.min().inclusive() ? Rel.GE : Rel.GT, kinds);
        }
        if (bounds.max() != null) {
            out = out.assume(form.minus(LinearForm.constant(count(bounds.max()))),
                    bounds.max().inclusive() ? Rel.LE : Rel.LT, kinds);
        }
        return out;
    }

    private static java.math.BigDecimal count(Endpoint end) {
        return Count.number(end.at()).at();
    }

    /**
     * An atom recorded as arithmetic over itself.
     *
     * <p>Nothing a program can write reaches this: a recipe is recorded over the parts a value was
     * built from, and a part is a strictly smaller expression. What it says is that the naming built
     * an atom out of itself, which is the check disagreeing with itself about which value an atom is
     * — so it is refused rather than swallowed, for the reason
     * {@link TheCheckDisagreesWithItself} gives.
     */
    static final class AnAtomComputedFromItself extends TheCheckDisagreesWithItself {

        private static final long serialVersionUID = 1L;

        AnAtomComputedFromItself(Term atom) {
            super("atom `" + atom.rendered() + "` is computed from itself");
        }
    }
}
