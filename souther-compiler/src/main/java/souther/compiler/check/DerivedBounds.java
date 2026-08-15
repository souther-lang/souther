package souther.compiler.check;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.Intervals;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;

import java.util.HashMap;
import java.util.LinkedHashSet;
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
     * {@code base} with what follows about every atom {@code terms} recorded a derivation for taken
     * as holding.
     */
    static NumericDomain<Term> refine(NumericDomain<Term> base, Terms terms) {
        Map<Term, Derivation> recipes = terms.derivations();
        if (recipes.isEmpty() || base.isBottom()) {
            return base;
        }
        Map<Term, Bounds> derived = new HashMap<>();
        for (Term atom : recipes.keySet()) {
            derive(atom, base, terms, derived, new LinkedHashSet<>());
        }
        NumericDomain<Term> out = base;
        for (Map.Entry<Term, Bounds> one : derived.entrySet()) {
            out = taking(out, one.getKey(), one.getValue(), terms);
        }
        return out;
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
            throw new IllegalStateException("atom `" + atom.rendered() + "` is computed from itself");
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
}
