package souther.compiler.check;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Intervals;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;

import java.math.BigDecimal;
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
 * <p>A product of two values, a truncating quotient and the remainder it leaves are not linear, so
 * the domain holds them as atoms and knows nothing of them. What their operands lie between it does
 * know, and that is enough to say something — so this reads the operands out of a domain, puts the
 * arithmetic through {@link Intervals}, and hands back the domain with what came out taken as
 * holding. A reduction's answer is an atom for a different reason — it is what a library operation
 * computed by applying a closure over and over — and it is bounded by {@link InductiveBounds} rather
 * than by a projection. The two are one walk here because a fold's seed may be a product and a
 * product's factor may be a fold, and one graph with one memo is what keeps either from being
 * derived twice.
 *
 * <p><b>A range is not the whole of what a recipe says.</b> A quotient's own range comes off its
 * operands' and says nothing about what it divides, so a remainder — the thing every step of a
 * change-making loop is built on — was a value nothing put at or above nought (#960). What relates
 * the two is {@code 0 <= a - b * (a / b) < b} under the sign facts the path establishes, which is a
 * rule over two positions and not a range either of them has. So what a recipe answers with is a
 * list of {@link Fact}s: a range where that is what it has to say, a relation where it has more.
 * Two shapes because the domain has two doors and each fact says which it goes through — a range's
 * ends read as assertions is {@link NumericDomain#assuming}'s reading and not a second one written
 * out here.
 *
 * <p>A projection and not an inference. Every fact is derived from the domain it was given, once,
 * and the results are taken in together at the end; nothing derived here is read back to derive
 * something else about the same atom. Letting a derived fact feed the next round would be interval
 * reasoning that tightens under its own answers — {@code x <= 0.5} giving {@code x * x <= 0.25}
 * giving a tighter {@code x} again — which is a different thing to build and a different thing to
 * state.
 *
 * <p>The domain is the argument, which is what keeps a derived fact the path's. The check reads a
 * construction twice, under what the guards established and under nothing, and the two get their
 * own answers here because they ask with their own domains.
 */
final class DerivedNumericFacts {

    private DerivedNumericFacts() {}

    /**
     * One thing a reading may take as holding about an atom, said the way the domain takes it in.
     *
     * <p>Two cases and not a record with two fields. A recipe that has only a range to give says one
     * {@link Between}; one that relates its atom to what it was computed from says as many
     * {@link Relating}s as it has relations, and adding a field per kind of thing a recipe might
     * one day say is how a list of facts turns into a shape nobody can add to.
     */
    sealed interface Fact {

        /** {@code atom} lies between {@code bounds}. */
        record Between(FactSubject atom, Bounds bounds) implements Fact {}

        /** {@code form rel 0}, over however many atoms the form names. */
        record Relating(LinearForm<FactSubject> form, Rel rel) implements Fact {}
    }

    /** At or above nought, as a range, for asking whether a reading put a value on that side. */
    private static final Bounds AT_OR_ABOVE_NOUGHT =
            new Bounds(Endpoint.inclusive(Count.ZERO), null);

    /** At or below it. */
    private static final Bounds AT_OR_BELOW_NOUGHT =
            new Bounds(null, Endpoint.inclusive(Count.ZERO));

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
     * {@code a * b / 100} reads what the product was derived to, and how the quotient in {@code
     * 額 - 額 / 100 * 100} reaches the construction over what it leaves. What does not happen is the
     * other direction — the reading is never rebuilt from what was derived and the recipes put
     * through again against it. Every derivation is handed {@code base} ({@link #derive} at every
     * level), so what is derived for an atom is a function of {@code base} and the recipe graph
     * alone: an evaluation over a graph with no way back to where it started, in whatever order the
     * roots are walked, with no fixed point to reach. A derived fact reaches another recipe only
     * where the graph names it, and never through a relation this domain holds between the two —
     * which is the interval reasoning that tightens under its own answers that this declines to be.
     */
    static NumericDomain<FactSubject> refine(NumericDomain<FactSubject> base, Terms terms, Set<FactSubject> asked) {
        Map<FactSubject, List<Fact>> derived = new LinkedHashMap<>();
        if ((!terms.derivations().isEmpty() || !terms.reductions().isEmpty()) && !base.isBottom()) {
            for (FactSubject atom : roots(terms, base, asked)) {
                derive(atom, base, terms, derived, new LinkedHashSet<>());
            }
        }
        watched(derived.keySet());
        NumericDomain<FactSubject> out = base;
        for (List<Fact> facts : derived.values()) {
            out = taking(out, facts, terms);
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

    /** Records the recipes this reading evaluated, where a test is reading them. Every atom here
     * had its recipe put through {@link Intervals}: {@link #derive} answers a second ask from what
     * it remembered, so an atom is written once however many forms name it. */
    private static void watched(Set<FactSubject> evaluated) {
        List<List<FactSubject>> watching = WATCHING;
        if (watching != null) {
            watching.add(List.copyOf(evaluated));
        }
    }

    /**
     * What is known of {@code atom}, computed once and remembered.
     *
     * <p>{@code deriving} holds what this is in the middle of answering. An atom is recorded against
     * arithmetic over the parts it was built from, and a part is a strictly smaller expression, so
     * the recipes make a graph with no way back to where it started; reaching one that is already
     * being answered would mean the naming built an atom out of itself.
     */
    private static List<Fact> derive(FactSubject atom, NumericDomain<FactSubject> base, Terms terms,
                                     Map<FactSubject, List<Fact>> done, Set<FactSubject> deriving) {
        List<Fact> had = done.get(atom);
        if (had != null) {
            return had;
        }
        if (!deriving.add(atom)) {
            throw new AnAtomComputedFromItself(atom);
        }
        List<Fact> facts = factsFor(atom, base, terms, done, deriving);
        deriving.remove(atom);
        done.put(atom, facts);
        return facts;
    }

    /**
     * What is known of {@code atom}, by whichever of the two things recorded about it says so.
     *
     * <p>Arithmetic outside the fragment is put through {@link Intervals}, which is a projection of
     * what its operands lie between, and through the relations a division states about what it
     * divided. A walk's answer is put through {@link InductiveBounds}, which proves a range holds it
     * by checking one step. Both read the same {@code base} and neither reads what the other
     * answered about the same atom, so the two compose the way the recipe graph does: a fold whose
     * seed is a product reaches the product through the form its walk was recorded with, and a
     * product of two folds reaches them through its factors.
     */
    private static List<Fact> factsFor(FactSubject atom, NumericDomain<FactSubject> base, Terms terms,
                                       Map<FactSubject, List<Fact>> done, Set<FactSubject> deriving) {
        InductiveBounds.Walk walk = terms.reductions().get(atom);
        if (walk != null) {
            // Each reading of the walk's own forms gets a memo of its own, since each is against a
            // different domain — the caller's, and the caller's with a candidate assumed. What is
            // shared is `deriving`, which is what says an atom was built out of itself, and that is
            // true of a recipe whatever domain it is read in.
            return between(atom, InductiveBounds.provenOf(walk, base, terms,
                    (form, domain) -> boundsOf(form, domain, terms, new LinkedHashMap<>(), deriving)));
        }
        return switch (terms.derivations().get(atom)) {
            case Derivation.Product product -> between(atom, Intervals.product(
                    boundsOf(product.left(), base, terms, done, deriving),
                    boundsOf(product.right(), base, terms, done, deriving)));
            case Derivation.TruncatingQuotient quotient ->
                    quotient(atom, quotient, base, terms, done, deriving);
            case Derivation.TruncatingRemainder remainder ->
                    remainder(atom, remainder, base, terms, done, deriving);
        };
    }

    /** One fact: the atom lies between those ends. */
    private static List<Fact> between(FactSubject atom, Bounds bounds) {
        return List.of(new Fact.Between(atom, bounds));
    }

    /**
     * What a truncating divide answers, under what this reading holds of the two it was computed
     * from: where it lies, and how it stands to what it divided.
     *
     * <p><b>Whether anything applies is decided here, and it is two questions.</b> The divisor is
     * read twice over: what the path proves of it, and what the operator's divisor can be at all
     * ({@link Derivation.TruncatingQuotient#divisorExtent}). The second is not a sharpening of the
     * first — a form is composed over numbers of any size, so what a reading proves of one can be a
     * range of numbers the operand never is. Where the two share nothing, this operator has no
     * divisor here. Where they share values but zero is among them, it has one and this rule says
     * nothing about it: what a divide by a range straddling zero comes to depends on how the values
     * are spaced, and a rule stated over the ends of a range is not a rule that can answer for it.
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
    private static List<Fact> quotient(FactSubject atom, Derivation.TruncatingQuotient quotient,
                                       NumericDomain<FactSubject> base, Terms terms,
                                       Map<FactSubject, List<Fact>> done,
                                       Set<FactSubject> deriving) {
        Bounds divisor = divisorOf(quotient.divisor(), quotient.divisorExtent(), base, terms, done,
                deriving);
        if (divisor == null) {
            return List.of();
        }
        Bounds numerator = boundsOf(quotient.numerator(), base, terms, done, deriving);
        List<Fact> facts = new ArrayList<>();
        facts.add(new Fact.Between(atom, Intervals.truncatingQuotient(numerator, divisor)));
        // What the divide left is `a - b * q`, which is a form the domain carries only where the
        // divisor is a number: against a divisor the reading holds in a range, `b * q` is a product
        // of two values and relating the quotient to what it divided would mean deriving that
        // product — from a range this rule has just derived, which is the reading that tightens
        // under its own answers.
        BigDecimal by = constantOf(quotient.divisor());
        if (by != null) {
            facts.addAll(leftOver(
                    quotient.numerator().minus(LinearForm.<FactSubject>atom(atom).times(by)),
                    by, numerator));
        }
        return facts;
    }

    /**
     * What a truncating remainder answers: where it lies, and on which side of nought.
     *
     * <p>The same two questions about the divisor, for the same reasons — a remainder by zero is a
     * value the operation does not produce, and one by a divisor a form names and the operand never
     * is is not this operation's remainder either. What is said under them is what truncation toward
     * zero means: the answer keeps the sign of what was divided, and is smaller than the divisor.
     */
    private static List<Fact> remainder(FactSubject atom, Derivation.TruncatingRemainder remainder,
                                        NumericDomain<FactSubject> base, Terms terms,
                                        Map<FactSubject, List<Fact>> done,
                                        Set<FactSubject> deriving) {
        Bounds divisor = divisorOf(remainder.divisor(), remainder.divisorExtent(), base, terms, done,
                deriving);
        if (divisor == null) {
            return List.of();
        }
        return leftOver(LinearForm.atom(atom), constantOf(remainder.divisor()),
                boundsOf(remainder.numerator(), base, terms, done, deriving));
    }

    /**
     * What holds of {@code left}, the part of a dividend a truncating divide leaves — whether it is
     * the value a remainder answered or the difference a quotient makes with what it divided.
     *
     * <p>Two halves, and each is stated where what it needs holds.
     *
     * <p>The sign is the dividend's. {@code /} over {@code Int} truncates toward zero (spec
     * §stdlib-int), so what is left keeps the sign of what was divided — {@code -7 / 2} is
     * {@code -3} and {@code -7 - 2 * -3} is {@code -1} — and a rule stated without the sign facts
     * would be wrong for every negative dividend. Which side the dividend is on is a fact about the
     * path and is read here, where the clause is read, exactly as a product's bound is; a reading
     * that puts it on neither side gets neither half, which is a rule not applying rather than a
     * rule saying nothing.
     *
     * <p>The magnitude is below the divisor's, and that half needs the divisor as a number ({@code
     * divisor} is null where the reading has none). A
     * divisor the reading holds in a range is not enough: what is left is smaller than the divisor
     * <em>it was divided by</em>, and the largest of a range is the only one of them a rule stated
     * over ends could use — which for a range open above is no number at all. So it is stated where
     * the divisor reads as a constant, which is where {@code Int.floorMod} states its own ends
     * (spec §invariant-discharge-guarantees) and for the same reason.
     */
    private static List<Fact> leftOver(LinearForm<FactSubject> left, BigDecimal divisor,
                                       Bounds dividend) {
        List<Fact> facts = new ArrayList<>();
        if (dividend.liesWithin(AT_OR_ABOVE_NOUGHT)) {
            facts.add(new Fact.Relating(left, Rel.GE));
        }
        if (dividend.liesWithin(AT_OR_BELOW_NOUGHT)) {
            facts.add(new Fact.Relating(left, Rel.LE));
        }
        if (divisor != null) {
            BigDecimal magnitude = divisor.abs();
            facts.add(new Fact.Relating(
                    left.minus(LinearForm.constant(magnitude)), Rel.LT));
            facts.add(new Fact.Relating(
                    left.plus(LinearForm.constant(magnitude)), Rel.GT));
        }
        return facts;
    }

    /** The number {@code form} is, or null where it names one this reading does not hold as a
     * written number. */
    private static BigDecimal constantOf(LinearForm<FactSubject> form) {
        return form.coefs().isEmpty() ? form.constant() : null;
    }

    /** What the operator divided by, or null where this rule has no divisor to fire on — see
     * {@link #quotient}. */
    private static Bounds divisorOf(LinearForm<FactSubject> form, Bounds extent,
                                    NumericDomain<FactSubject> base, Terms terms,
                                    Map<FactSubject, List<Fact>> done, Set<FactSubject> deriving) {
        Bounds divisor = boundsOf(form, base, terms, done, deriving).meet(extent);
        return !divisor.holdsAValue() || divisor.admits(Count.ZERO) ? null : divisor;
    }

    /**
     * What {@code form} lies between, with whatever was derived about its own atoms taken in first.
     *
     * <p>A factor may itself be a product — {@code a * b / 100} is one — and what the domain proves
     * about such an atom is nothing at all until the arithmetic under it has been read. Only the
     * atoms this form names are derived, so what is read is the expression's own structure and not
     * everything else the reading has recorded.
     */
    private static Bounds boundsOf(LinearForm<FactSubject> form, NumericDomain<FactSubject> base, Terms terms,
                                   Map<FactSubject, List<Fact>> done, Set<FactSubject> deriving) {
        NumericDomain<FactSubject> with = base;
        for (FactSubject atom : form.coefs().keySet()) {
            if (recorded(terms, atom)) {
                with = taking(with, derive(atom, base, terms, done, deriving), terms);
            }
        }
        return with.boundsOf(form);
    }

    /** {@code d} with every one of {@code facts} taken as holding, each through the door it names.
     * An end a range does not reach is asserted as the strict comparison it is, which is what the
     * domain reads a range's ends as. */
    private static NumericDomain<FactSubject> taking(NumericDomain<FactSubject> d, List<Fact> facts,
                                                     Terms terms) {
        NumericDomain<FactSubject> out = d;
        for (Fact fact : facts) {
            out = switch (fact) {
                case Fact.Between(FactSubject atom, Bounds bounds) ->
                        out.assuming(atom, bounds, terms.kindsOf(LinearForm.atom(atom)));
                case Fact.Relating(LinearForm<FactSubject> form, Rel rel) ->
                        out.assume(form, rel, terms.kindsOf(form));
            };
        }
        return out;
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
