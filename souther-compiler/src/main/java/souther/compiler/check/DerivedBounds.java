package souther.compiler.check;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Intervals;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.numeric.NumericDomain.LinearForm;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What follows about the values the domain holds as atoms: arithmetic outside the affine fragment,
 * and what a walk over a container answers.
 *
 * <p>A product of two values and a truncating quotient are not linear, so the domain holds them as
 * atoms and knows nothing of them. What their factors lie between it does know, and that is enough
 * to bound them — so this reads the factors out of a domain, puts the arithmetic through
 * {@link Intervals}, and hands back the domain with what came out taken as holding. A value that is
 * one of several is an atom for a reason of its own — nothing composes an {@code if} — and it is
 * bounded by the range its arms span. A reduction's answer is one for a third reason, being what a
 * library operation computed by applying a closure over and over, and it is bounded by
 * {@link InductiveBounds} rather than by a projection. They are one walk here because a fold's seed
 * may be a product and a product's factor may be a fold and an arm may be either, and one graph with
 * one memo is what keeps any of them from being derived twice.
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
     *
     * <p>A reading is one evaluation of the recipes against one domain, and a walk's own readings
     * are among them: what a step names is evaluated there and nowhere else, so a walk whose
     * readings were unwatched would be exactly where the memo could stop holding unremarked. What
     * the memo makes true is a claim about one reading and not about a body — a recipe asked twice
     * under two domains is evaluated twice and rightly so, and what may not happen is the same
     * recipe evaluated twice for one of them.
     */
    static List<List<FactSubject>> WATCHING;

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
     * <p>One pass, and not because the roots happen not to grow. The recipe graph's own edges do
     * carry: a recipe's operands are derived first and read where its form is read, which is how
     * {@code a * b / 100} reads what the product was derived to. What does not happen is the other
     * direction — the reading is never rebuilt from what was derived and the recipes put through
     * again against it. Every derivation is handed {@code base} ({@link #derive} at every level), so
     * what is derived for an atom is a function of {@code base} and the recipe graph alone: an
     * evaluation over a graph with no way back to where it started, in whatever order the roots are
     * walked, with no fixed point to reach. A derived bound reaches another recipe only where the
     * graph names it, and never through a relation this domain holds between the two — which is the
     * interval reasoning that tightens under its own answers that this declines to be.
     */
    static NumericDomain<FactSubject> refine(NumericDomain<FactSubject> base, Terms terms, Set<FactSubject> asked) {
        Memo derived = new Memo();
        if ((!terms.derivations().isEmpty() || !terms.reductions().isEmpty()) && !base.isBottom()) {
            for (FactSubject atom : roots(terms, base, asked)) {
                derive(atom, base, terms, derived, new LinkedHashSet<>());
            }
        }
        derived.watched();
        NumericDomain<FactSubject> out = base;
        for (Map.Entry<FactSubject, Bounds> one : derived.answered.entrySet()) {
            out = taking(out, one.getKey(), one.getValue(), terms);
        }
        return out;
    }

    /** Whether {@code atom} was recorded as anything this can derive from — arithmetic outside the
     * fragment, or the answer of a walk. Two tables and one question: what a reading walks is the
     * atoms it can reach that anything was recorded about. */
    private static boolean recorded(Terms terms, FactSubject atom) {
        return terms.derivations().containsKey(atom) || terms.reductions().containsKey(atom);
    }

    /** The atoms this reading is to derive from: the ones it can reach that anything was recorded
     * about. Walked from the reaching side rather than from the tables, so what it costs is what the
     * question is about and not how much arithmetic the behavior contains. */
    private static Set<FactSubject> roots(Terms terms, NumericDomain<FactSubject> base,
                                   Set<FactSubject> asked) {
        Set<FactSubject> out = new LinkedHashSet<>();
        for (FactSubject atom : asked) {
            if (recorded(terms, atom)) {
                out.add(atom);
            }
        }
        for (FactSubject atom : base.atomsSpokenOf()) {
            if (recorded(terms, atom)) {
                out.add(atom);
            }
        }
        return out;
    }

    /**
     * What one reading has answered, and the recipes it evaluated to answer it.
     *
     * <p>Two halves and not one, because they say different things. What was answered is what a
     * second ask of the same atom comes back with, which is what makes the recipes an evaluation over
     * a graph rather than over the tree of paths through it. What was evaluated is how much of that
     * was done, and it is a list because an atom appearing twice in it is the memo not holding —
     * which is exactly what a set cannot say. Counted where a recipe is really put through, past the
     * answer a second ask comes back with, so what it holds is work and not asks.
     *
     * <p>The second half is kept only while a test is reading it. Every compilation would otherwise
     * write a value per recipe evaluated for nobody, and a hook a compilation pays for is one its
     * answer could come to depend on.
     */
    private static final class Memo {

        private final Map<FactSubject, Bounds> answered = new LinkedHashMap<>();

        /** Null wherever no test is reading, which is every compilation but a test's. Kept as
         * whether-to-record rather than as a list nobody reads, for the reason
         * {@link InvariantChecker#OPENING} is: a hook that costs a compilation something is one the
         * answer could come to depend on, and this one records a value per recipe evaluated. */
        private final List<FactSubject> evaluated = WATCHING == null ? null : new ArrayList<>();

        void evaluating(FactSubject atom) {
            if (evaluated != null) {
                evaluated.add(atom);
            }
        }

        void watched() {
            if (evaluated != null) {
                WATCHING.add(List.copyOf(evaluated));
            }
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
    private static Bounds derive(FactSubject atom, NumericDomain<FactSubject> base, Terms terms,
                                 Memo done, Set<FactSubject> deriving) {
        Bounds had = done.answered.get(atom);
        if (had != null) {
            return had;
        }
        if (!deriving.add(atom)) {
            throw new AnAtomComputedFromItself(atom);
        }
        done.evaluating(atom);
        Bounds bounds = boundsFor(atom, base, terms, done, deriving);
        deriving.remove(atom);
        done.answered.put(atom, bounds);
        return bounds;
    }

    /**
     * What {@code atom} lies between, by whichever of the things recorded about it says so.
     *
     * <p>Arithmetic outside the fragment is put through {@link Intervals}, which is a projection of
     * what its operands lie between. A choice is spanned by its arms. A walk's answer is put through
     * {@link InductiveBounds}, which proves a range holds it by checking one step. Each reads the
     * same {@code base} and none reads what another answered about the same atom, so they compose the
     * way the recipe graph does:
     * a fold whose seed is a product reaches the product through the form its walk was recorded with,
     * and a product of two folds reaches them through its factors.
     */
    private static Bounds boundsFor(FactSubject atom, NumericDomain<FactSubject> base, Terms terms,
                                    Memo done, Set<FactSubject> deriving) {
        InductiveBounds.Walk walk = terms.reductions().get(atom);
        if (walk != null) {
            // Each reading of the walk's own forms gets a memo of its own, since each is against a
            // different domain — the caller's, and the caller's with a candidate assumed. What is
            // shared is `deriving`, which is what says an atom was built out of itself, and that is
            // true of a recipe whatever domain it is read in.
            return InductiveBounds.provenOf(walk, base, terms, (form, domain) -> {
                Memo memo = new Memo();
                Bounds answer = boundsOf(form, domain, terms, memo, deriving);
                // A reading, and watched as one. What the walk reads is where a step's own recipes
                // are evaluated, so a reading that could not be seen here was the one place the
                // memo could stop holding without anything saying so.
                memo.watched();
                return answer;
            });
        }
        return switch (terms.derivations().get(atom)) {
            case Derivation.Product product -> Intervals.product(
                    boundsOf(product.left(), base, terms, done, deriving),
                    boundsOf(product.right(), base, terms, done, deriving));
            case Derivation.Quotient quotient -> quotient(quotient, base, terms, done, deriving);
            case Derivation.Chosen chosen -> chosen(chosen, base, terms, done, deriving);
        };
    }

    /**
     * What a value that is one of several lies between: the range holding what every arm answers.
     *
     * <p>The value is one of the arms, so a range holding all of them holds it. Which arm it is
     * depends on what chose it and this does not read that ({@link Derivation.Chosen}), so every arm
     * counts and none is ruled out — an arm the reading says nothing about leaves the whole choice
     * unbounded, which is what an arm nothing is known of comes to.
     *
     * <p>There is always an arm, so there is always a range: a choice is one of several and holding
     * none is refused where a recipe is built rather than answered for here. A reader that took an
     * empty list for a range with no ends would go on bounding nothing while the disagreement that
     * produced it went unremarked.
     *
     * <p>Each arm is read against the domain this was handed, and the arms are read one after
     * another out of the same memo. So a choice inside an arm is derived once however many arms
     * stand over it, and the nesting costs what the recipes cost and not what a reading of every
     * path through them would.
     */
    private static Bounds chosen(Derivation.Chosen chosen, NumericDomain<FactSubject> base,
                                 Terms terms, Memo done,
                                 Set<FactSubject> deriving) {
        List<LinearForm<FactSubject>> arms = chosen.arms();
        Bounds out = boundsOf(arms.get(0), base, terms, done, deriving);
        for (LinearForm<FactSubject> arm : arms.subList(1, arms.size())) {
            out = Bounds.spanning(out, boundsOf(arm, base, terms, done, deriving));
        }
        return out;
    }

    /**
     * What a truncating divide lies between, under what this reading holds of the two it was
     * computed from.
     *
     * <p><b>Whether the rule applies is decided here, and it is two questions.</b> The divisor is
     * read twice over: what the path proves of it, and what the operator's divisor can be at all
     * ({@link Derivation.Quotient#divisorExtent}). The second is not a sharpening of the first — a
     * form is composed over numbers of any size, so what a reading proves of one can be a range of
     * numbers the operand never is. Where the two share nothing, this operator has no divisor here.
     * Where they share values but zero is among them, it has one and this rule says nothing about
     * it: what a divide by a range straddling zero comes to depends on how the values are spaced,
     * and a rule stated over the ends of a range is not a rule that can answer for it.
     *
     * <p>Neither answer is a claim about the quotients. In particular the second is not a statement
     * that they run past every value: over the whole numbers a divisor between zero and five divides
     * by one at the nearest, and the successful divides are bounded. What is said is that this rule
     * does not establish where they are — which is what an unapplied rule contributes, and is not
     * the same thing as a bound.
     *
     * <p><b>Nothing derived, and not an empty range.</b> That a rule has no operands to fire on is
     * not a proof that the path has no execution: read as an empty range it would be taken into the
     * domain as a contradiction, and a contradictory domain proves every clause there is — so a
     * construction nothing here can read would come out discharged rather than owed.
     *
     * <p>The dividend is not held to its own extent. It could be, and it would be sound; it would
     * also be a sharpening of a bound that is already sound, which is a different reason from the
     * one above and not one this rule needs.
     */
    private static Bounds quotient(Derivation.Quotient quotient, NumericDomain<FactSubject> base,
                                   Terms terms, Memo done,
                                   Set<FactSubject> deriving) {
        Bounds divisor = boundsOf(quotient.divisor(), base, terms, done, deriving)
                .meet(quotient.divisorExtent());
        if (!divisor.holdsAValue() || divisor.admits(Count.ZERO)) {
            return new Bounds(null, null);
        }
        return Intervals.truncatingQuotient(
                boundsOf(quotient.numerator(), base, terms, done, deriving), divisor);
    }

    /**
     * What {@code form} lies between, with whatever its own atoms were derived to taken in first.
     *
     * <p>A factor may itself be a product — {@code a * b / 100} is one — and what the domain proves
     * about such an atom is nothing at all until the arithmetic under it has been read. Only the
     * atoms this form names are derived, so what is read is the expression's own structure and not
     * everything else the reading has recorded.
     */
    private static Bounds boundsOf(LinearForm<FactSubject> form, NumericDomain<FactSubject> base, Terms terms,
                                   Memo done, Set<FactSubject> deriving) {
        NumericDomain<FactSubject> with = base;
        for (FactSubject atom : form.coefs().keySet()) {
            if (recorded(terms, atom)) {
                with = taking(with, atom, derive(atom, base, terms, done, deriving), terms);
            }
        }
        return with.boundsOf(form);
    }

    /** {@code d} with {@code atom} taken to lie between {@code bounds}. An end the range does not
     * reach is asserted as the strict comparison it is, which is what the domain reads a range's
     * ends as. */
    private static NumericDomain<FactSubject> taking(NumericDomain<FactSubject> d, FactSubject atom, Bounds bounds,
                                              Terms terms) {
        return d.assuming(atom, bounds, terms.kindsOf(LinearForm.atom(atom)));
    }

    /**
     * An atom recorded as arithmetic over itself.
     *
     * <p>Nothing a program can write reaches this: a recipe is recorded over the parts a value was
     * built from, and a part is a strictly smaller expression. What it says is that the naming built
     * an atom out of itself, which is the check disagreeing with itself about which value an atom is
     * — so it is refused rather than swallowed, for the reason
     * {@link TheCheckDisagreesWithItself} gives.
     *
     * <p>Asked of what a reading walks, and so of the recipes its question reaches rather than of
     * every recipe the naming recorded. A cycle among recipes no reading reaches goes unremarked,
     * which is a narrowing of where an assertion about this check's own naming can fire and not of
     * what any program is told: what such a recipe would have derived is read by nothing.
     */
    static final class AnAtomComputedFromItself extends TheCheckDisagreesWithItself {

        private static final long serialVersionUID = 1L;

        AnAtomComputedFromItself(FactSubject atom) {
            super("atom `" + atom.rendered() + "` is computed from itself");
        }
    }
}
