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
 * holding. A value that is one of several is an atom for a reason of its own — nothing composes an
 * {@code if} — and it is bounded by the range its arms span. A reduction's answer is one for a third
 * reason, being what a library operation computed by applying a closure over and over, and it is
 * bounded by {@link InductiveBounds} rather than by a projection. They are one walk here because a
 * fold's seed may be a product and a product's factor may be a fold and an arm may be either, and
 * one graph with one memo is what keeps any of them from being derived twice.
 *
 * <p><b>A range is not the whole of what a recipe says.</b> A quotient's own range comes off its
 * operands' and says nothing about what it divides, so a remainder — the thing every step of a
 * change-making loop is built on — was a value nothing put at or above nought (#960). What relates
 * the two is that what a divide leaves keeps the dividend's sign and is smaller than the divisor's
 * magnitude — {@code 0 <= a - b * (a / b) < b} where the dividend is at or above nought and the
 * divisor above it — which is a rule over two positions and not a range either of them has. So what a recipe answers with is a
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
    sealed interface Fact permits Fact.Between, NumericConstraint {

        /** {@code atom} lies between {@code bounds}. */
        record Between(FactSubject atom, Bounds bounds) implements Fact {}
    }

    /**
     * What a recipe answers about the atom it was recorded for.
     *
     * <p>Three answers, where two of them used to be the empty list. A rule with nothing to fire on
     * says nothing — the divisor is a range holding zero, the scale is not one number, the operands
     * are values this reading has no bound for — and a rule that fired and found the arithmetic
     * running wholly outside what the answer's own kind of number holds says something quite
     * different: this operation produces no value at all for the operands admitted here. Told apart
     * only by which of them a caller asked for, the second reached every caller as the first, and
     * the one thing it says was the one thing nobody could read.
     *
     * <p>{@link NoValueCameOfIt} is about the recipe's <em>normal</em> answer and about nothing more.
     * An operation that answers a union produces no number where it comes back as its other case
     * either, and that case is one an arm is reached at; whether the operation completes at all is a
     * question with the other cases in it, and it is asked where they are known and not here.
     *
     * <p>Not an empty range in the domain, which is the shape this is written to avoid. Asserted
     * there it would be a contradiction, and a contradictory domain proves every clause there is —
     * so a construction over a value nothing is known of would come out discharged. It would not
     * even be that consistently: what refuses a clause is not the numeric rules alone, so the
     * construction would come out established by the numbers and refused by the predicates at once,
     * which is the check disagreeing with itself rather than answering.
     */
    sealed interface Says {

        /** Nothing this rule can say here. */
        record Nothing() implements Says {}

        /** What the rule found, each fact through the door it names. */
        record These(List<Fact> facts) implements Says {}

        /**
         * The arithmetic ran wholly outside what {@code atom}'s own kind of number holds, so the
         * operation answered no value for any operands this reading admits.
         *
         * <p>Read of the carrier and not of a declaration. A value of a newtype has satisfied that
         * newtype's invariant, and whether a construction does is the question being asked — so what
         * is read is the machine's range, which is true of every value that exists at all.
         */
        record NoValueCameOfIt(FactSubject atom) implements Says {}

        Says NOTHING = new Nothing();

        /** The facts this holds, which is none but where a rule found some. */
        default List<Fact> facts() {
            return this instanceof These(List<Fact> found) ? found : List.of();
        }
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
     *
     * <p>A reading is one evaluation of the recipes against one domain, and a walk's own readings
     * are among them: what a step names is evaluated there and nowhere else, so a walk whose
     * readings were unwatched would be exactly where the memo could stop holding unremarked. What
     * the memo makes true is a claim about one reading and not about a body — a recipe asked twice
     * under two domains is evaluated twice and rightly so, and what may not happen is the same
     * recipe evaluated twice for one of them.
     */
    static List<Reading> WATCHING;

    /**
     * What a reading was asked for, and the recipes it evaluated answering it.
     *
     * <p>The question is beside the atoms because two questions are asked of these recipes and each
     * has its own thing to hold. What a construction's reading evaluates is what its clauses reach,
     * and it must not grow with arithmetic the construction is not about. What an evaluation's own
     * reading evaluates is that evaluation's recipe, and there is one of those per operation the
     * walk reaches — so the two counts move with different things, and a list that ran them together
     * could not say either.
     */
    record Reading(Question asked, List<FactSubject> evaluated) {}

    /** Why a reading was made. */
    enum Question {
        /** What the clauses of one construction reach ({@link #refine}). */
        WHAT_A_CONSTRUCTION_IS_JUDGED_AGAINST,
        /** Whether one operation answers a value ({@link #saysOf}). */
        WHETHER_AN_OPERATION_ANSWERS
    }

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
        Memo derived = new Memo(Question.WHAT_A_CONSTRUCTION_IS_JUDGED_AGAINST);
        if ((!terms.derivations().isEmpty() || !terms.reductions().isEmpty()) && !base.isBottom()) {
            for (FactSubject atom : roots(terms, base, asked)) {
                derive(atom, base, terms, derived, new LinkedHashSet<>(), ContextMultiplicity.ofOneReading());
            }
        }
        derived.watched();
        NumericDomain<FactSubject> out = base;
        for (Says said : derived.answered.values()) {
            out = taking(out, said, terms);
        }
        return out;
    }

    /**
     * What the recipe recorded for {@code atom} says about it, under {@code base} alone.
     *
     * <p>One atom, where {@link #refine} answers a domain over everything a question reaches. The
     * caller is asking about the operation that computed this value and about nothing else, and a
     * domain would answer that by not mentioning it: what a recipe found and what it could not say
     * both leave the domain as it was. It is the {@link Says} that is wanted, so it is the
     * {@link Says} that comes back.
     *
     * <p>A reading of its own, with a memo of its own, because it is against a domain of its own —
     * the walk's, where it stands. What the memo makes true is a claim about one reading, so this
     * is watched as one.
     */
    static Says saysOf(FactSubject atom, NumericDomain<FactSubject> base, Terms terms) {
        if (!recorded(terms, atom) || base.isBottom()) {
            return Says.NOTHING;
        }
        Memo memo = new Memo(Question.WHETHER_AN_OPERATION_ANSWERS);
        Says said = derive(atom, base, terms, memo, new LinkedHashSet<>(),
                ContextMultiplicity.ofOneReading());
        memo.watched();
        return said;
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

        private final Question asked;

        private final Map<FactSubject, Says> answered = new LinkedHashMap<>();

        Memo(Question asked) {
            this.asked = asked;
        }

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
                WATCHING.add(new Reading(asked, List.copyOf(evaluated)));
            }
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
    private static Says derive(FactSubject atom, NumericDomain<FactSubject> base, Terms terms,
                               Memo done, Set<FactSubject> deriving, ContextMultiplicity copies) {
        Says had = done.answered.get(atom);
        if (had != null) {
            return had;
        }
        if (!deriving.add(atom)) {
            throw new AnAtomComputedFromItself(atom);
        }
        done.evaluating(atom);
        Says said = factsFor(atom, base, terms, done, deriving, copies);
        deriving.remove(atom);
        done.answered.put(atom, said);
        return said;
    }

    /**
     * What is known of {@code atom}, by whichever of the things recorded about it says so.
     *
     * <p>Arithmetic outside the fragment is put through {@link Intervals}, which is a projection of
     * what its operands lie between, and through the relations a division states about what it
     * divided. A choice is spanned by its arms. A walk's answer is put through
     * {@link InductiveBounds}, which proves a range holds it by checking one step. Each reads the
     * same {@code base} and none reads what another answered about the same atom, so they compose
     * the way the recipe graph does: a fold whose
     * seed is a product reaches the product through the form its walk was recorded with, and a
     * product of two folds reaches them through its factors.
     */
    private static Says factsFor(FactSubject atom, NumericDomain<FactSubject> base, Terms terms,
                                 Memo done, Set<FactSubject> deriving, ContextMultiplicity copies) {
        InductiveBounds.Walk walk = terms.reductions().get(atom);
        if (walk != null) {
            // Each reading of the walk's own forms gets a memo of its own, since each is against a
            // different domain — the caller's, and the caller's with a candidate assumed. What is
            // shared is `deriving`, which is what says an atom was built out of itself, and that is
            // true of a recipe whatever domain it is read in.
            return between(atom, InductiveBounds.provenOf(walk, base, terms, (form, domain) -> {
                Memo memo = new Memo(done.asked);
                Bounds answer = boundsOf(form, domain, terms, memo, deriving, copies);
                // A reading, and watched as one. What the walk reads is where a step's own recipes
                // are evaluated, so a reading that could not be seen here was the one place the
                // memo could stop holding without anything saying so.
                memo.watched();
                return answer;
            }), terms);
        }
        return switch (terms.derivations().get(atom)) {
            case Derivation.Product product -> projected(atom, Intervals.product(
                    boundsOf(product.left(), base, terms, done, deriving, copies),
                    boundsOf(product.right(), base, terms, done, deriving, copies)), terms);
            case Derivation.TruncatingQuotient quotient ->
                    quotient(atom, quotient, base, terms, done, deriving, copies);
            case Derivation.TruncatingRemainder remainder ->
                    remainder(atom, remainder, base, terms, done, deriving, copies);
            case Derivation.RoundedQuotient rounded ->
                    rounded(atom, rounded, base, terms, done, deriving, copies);
            case Derivation.Chosen chosen ->
                    between(atom, chosen(chosen, base, terms, done, deriving, copies), terms);
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
                                 Terms terms, Memo done, Set<FactSubject> deriving,
                                 ContextMultiplicity copies) {
        List<Derivation.Chosen.Arm> arms = chosen.arms();
        ContextMultiplicity inAnArm = copies.opening(contextsIn(arms));
        Bounds out = null;
        for (Derivation.Chosen.Arm arm : arms) {
            if (inAnArm == null || arm.settles().isEmpty()) {
                // Read where the caller is reading: the split was not opened, or this arm states
                // nothing this reader can use and so is not a reading of its own.
                out = spanned(out, boundsOf(arm.answer(), base, terms, done, deriving, copies));
                continue;
            }
            NumericDomain<FactSubject> under = stating(arm, base, terms);
            // An arm whose statements cannot all hold is an arm this choice never answers, so it
            // contributes no values to the span. Spanning with what it would have answered widens
            // the range by an arm that is not there — which is how a value every arm of which is
            // the accumulator stopped being the accumulator.
            if (under.isBottom()) {
                continue;
            }
            out = spanned(out, readingAnArm(arm, under, terms, done.asked, deriving, inAnArm));
        }
        if (out != null) {
            return out;
        }
        // Every arm's statements were refused together, which is a disagreement about reachability
        // this is not the reader to settle. Read them as they stand.
        for (Derivation.Chosen.Arm arm : arms) {
            out = spanned(out, boundsOf(arm.answer(), base, terms, done, deriving, copies));
        }
        return out;
    }

    private static Bounds spanned(Bounds out, Bounds answered) {
        return out == null ? answered : Bounds.spanning(out, answered);
    }

    /**
     * How many readings this choice comes to, which is what opening it would copy the reading into.
     *
     * <p>Asked of what this reader gets and not of how the choice was written. A split of arms is a
     * split of readings only where the arms are read against different domains; an arm that states
     * nothing this reader can use is read against the domain the caller was reading against, and is
     * that reading rather than a copy of it. So a conditional on a flag — {@code if x.on then …} —
     * comes to one, which {@link ContextMultiplicity} opens for nothing, and a clamp written inside
     * one is opened on its own terms rather than after a budget something numerically silent had
     * already spent.
     *
     * <p>Two arms stating the same relations are counted as two, since what makes two statements one
     * is a comparison of forms this does not make. That is a count too high and never too low, so it
     * spends budget where it need not and refuses nothing that a smaller count would have admitted
     * to be unsound.
     */
    private static int contextsIn(List<Derivation.Chosen.Arm> arms) {
        int stating = 0;
        boolean anySilent = false;
        for (Derivation.Chosen.Arm arm : arms) {
            if (arm.settles().isEmpty()) {
                anySilent = true;
            } else {
                stating++;
            }
        }
        return stating + (anySilent ? 1 : 0);
    }

    /** {@code base} with what choosing {@code arm} states taken as holding. */
    private static NumericDomain<FactSubject> stating(Derivation.Chosen.Arm arm,
                                                      NumericDomain<FactSubject> base, Terms terms) {
        NumericDomain<FactSubject> under = base;
        for (NumericConstraint settled : arm.settles()) {
            under = under.assume(settled.form(), settled.rel(), terms.kindsOf(settled.form()));
        }
        return under;
    }

    /** What one arm answers, read against {@code under}, out of a memo of its own.
     *
     * <p>A memo of its own because a memo is what one reading answered, and a reading is against one
     * domain: an atom answered under one arm's statements is not what it comes to under another's.
     * {@code deriving} is shared, since an atom built out of itself is built out of itself whatever
     * domain it is read in. */
    private static Bounds readingAnArm(Derivation.Chosen.Arm arm, NumericDomain<FactSubject> under,
                                       Terms terms, Question asked, Set<FactSubject> deriving,
                                       ContextMultiplicity copies) {
        Memo memo = new Memo(asked);
        Bounds answered = boundsOf(arm.answer(), under, terms, memo, deriving, copies);
        memo.watched();
        return answered;
    }

    /**
     * One fact: the atom lies between those ends, with an end the arithmetic put outside what its
     * own kind of number holds pulled back to where the values stop.
     *
     * <p>A recipe is arithmetic composed over numbers of any size, so what it works out to can be a
     * number the value it is about never is: the quotient of the smallest {@code Int} by minus one
     * works out to one past the whole-number range, and the operation that would have answered it
     * aborts instead (spec §stdlib-int). Left as it stood, that end is a value no run produces and
     * the reading can refuse a construction over it — which it did, as an error and on a path
     * nothing reaches.
     *
     * <p>A correction and not a range of its own ({@link Bounds#noFurtherOutThan}): an end the
     * arithmetic put nowhere stays nowhere. A range stated here would be one every reading holds,
     * the reading that assumed nothing included, and "within what an {@code Int} is" discharges
     * nothing while costing every derived atom two more rules to carry.
     *
     * <p>Said of every range a recipe answers with rather than in each recipe, so that a recipe
     * added later is held to it without being asked.
     *
     * <p><b>Where the correction leaves nothing, no range is stated — and not an empty one.</b>
     * Asserted as an empty range it would be a contradiction, and a contradictory domain proves
     * every clause there is; it would not even do that consistently, since what refuses a clause is
     * not the numeric rules alone, so a construction would come out established by the numbers and
     * refused by the predicates at once. What that emptiness <em>means</em> is a different question
     * and is not answered by leaving a range out: this says nothing about the atom, and
     * {@link #projected} is where a rule that put one operation's arithmetic through says the other
     * thing about it.
     */
    private static Says between(FactSubject atom, Bounds bounds, Terms terms) {
        Bounds held = heldToWhatItCanBe(atom, bounds, terms);
        return held.holdsAValue() ? new Says.These(List.of(new Fact.Between(atom, held)))
                : Says.NOTHING;
    }

    /**
     * The same, where {@code bounds} is a projection of the arithmetic one operation computes — so
     * an empty answer is that operation having produced no value rather than this reading having
     * found none.
     *
     * <p>Which is the one place the two can be told apart, and it is told apart by what was put
     * through rather than by what came out. A range that holds nothing before it meets the carrier
     * is a rule that proved nothing and is {@link Says.NOTHING}; a range that held values and lost
     * every one of them to the carrier is an operation whose every answer here is a number no value
     * of its type is, which is an abort (spec §stdlib-int) and not a value nothing is known of.
     *
     * <p>Asked of an operation and not of a choice or a walk. A choice answers one of its arms and
     * each arm is already an answer held to its own carrier, so an empty span there is arms this
     * reading could say nothing about; and what a walk proves is proved by checking a step, where
     * failing to prove a range is not proving there is no value in one.
     */
    private static Says projected(FactSubject atom, Bounds bounds, Terms terms) {
        if (!bounds.holdsAValue()) {
            return Says.NOTHING;
        }
        Bounds held = heldToWhatItCanBe(atom, bounds, terms);
        return held.holdsAValue() ? new Says.These(List.of(new Fact.Between(atom, held)))
                : new Says.NoValueCameOfIt(atom);
    }

    /** {@code bounds} with an end outside what {@code atom}'s own kind of number holds pulled back
     * to it — and holding no value where the arithmetic ran wholly outside it, which is what says
     * the operation produced none. */
    private static Bounds heldToWhatItCanBe(FactSubject atom, Bounds bounds, Terms terms) {
        Bounds extent = terms.extentOf(atom);
        return extent == null ? bounds : bounds.noFurtherOutThan(extent);
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
    private static Says quotient(FactSubject atom, Derivation.TruncatingQuotient quotient,
                                 NumericDomain<FactSubject> base, Terms terms,
                                 Memo done, Set<FactSubject> deriving, ContextMultiplicity copies) {
        Bounds divisor = divisorOf(quotient.divisor(), quotient.divisorExtent(), base, terms, done,
                deriving, copies);
        if (divisor == null) {
            return Says.NOTHING;
        }
        Bounds numerator = boundsOf(quotient.numerator(), base, terms, done, deriving, copies);
        Says where = projected(atom,
                Intervals.truncatingQuotient(numerator, divisor), terms);
        // Nothing at all, and not the halves that do not mention the range. What is left of a
        // dividend relates the quotient to it, so a reading that dropped where the quotient lies and
        // kept that relation would put the quotient back where the arithmetic had it — a number no
        // `Int` is, reached the long way round.
        if (!(where instanceof Says.These)) {
            return where;
        }
        List<Fact> facts = new ArrayList<>(where.facts());
        // What the divide left is `a - b * q`, which is a form the domain carries only where this
        // reading holds the divisor to one number: against a divisor left in a range, `b * q` is a
        // product of two values and relating the quotient to what it divided would mean deriving that
        // product — from a range this rule has just derived, which is the reading that tightens
        // under its own answers.
        BigDecimal by = theOneValueOf(divisor);
        if (by != null) {
            facts.addAll(leftOver(
                    quotient.numerator().minus(LinearForm.<FactSubject>atom(atom).times(by)),
                    divisor, numerator));
        }
        return new Says.These(List.copyOf(facts));
    }

    /**
     * What a truncating remainder answers: where it lies, and on which side of nought.
     *
     * <p>The same two questions about the divisor, for the same reasons — a remainder by zero is a
     * value the operation does not produce, and one by a divisor a form names and the operand never
     * is is not this operation's remainder either. What is said under them is what truncation toward
     * zero means: the answer keeps the sign of what was divided, and is smaller than the divisor.
     */
    private static Says remainder(FactSubject atom, Derivation.TruncatingRemainder remainder,
                                  NumericDomain<FactSubject> base, Terms terms,
                                  Memo done, Set<FactSubject> deriving, ContextMultiplicity copies) {
        Bounds divisor = divisorOf(remainder.divisor(), remainder.divisorExtent(), base, terms, done,
                deriving, copies);
        if (divisor == null) {
            return Says.NOTHING;
        }
        return new Says.These(leftOver(LinearForm.atom(atom), divisor,
                boundsOf(remainder.numerator(), base, terms, done, deriving, copies)));
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
     * <p>The magnitude is below the divisor's, and that half needs a number the divisor cannot be
     * further from nought than. It is read off what this reading holds the divisor to and not off
     * how the divisor was written: a name given a constant is that constant, and so is a value a
     * guard pins, which is how every other rule here reads a value
     * (spec §invariant-discharge-terms). Asked of the form instead, this said nothing wherever the
     * divisor was anything but a written number — under {@code guard b == 100} the two sign facts
     * arrived and the magnitude did not, though the reading held the divisor to one number a line
     * earlier. A range open either way leaves no such number and then the half is not stated, which
     * is the condition {@code Int.floorMod} states its own ends under
     * (spec §invariant-discharge-guarantees) and for the same reason.
     */
    private static List<Fact> leftOver(LinearForm<FactSubject> left, Bounds divisor,
                                       Bounds dividend) {
        List<Fact> facts = new ArrayList<>();
        if (dividend.liesWithin(AT_OR_ABOVE_NOUGHT)) {
            facts.add(new NumericConstraint(left, Rel.GE));
        }
        if (dividend.liesWithin(AT_OR_BELOW_NOUGHT)) {
            facts.add(new NumericConstraint(left, Rel.LE));
        }
        BigDecimal magnitude = noFurtherFromNoughtThan(divisor);
        if (magnitude != null) {
            facts.add(new NumericConstraint(left.minus(LinearForm.constant(magnitude)), Rel.LT));
            facts.add(new NumericConstraint(left.plus(LinearForm.constant(magnitude)), Rel.GT));
        }
        return facts;
    }

    /**
     * What a divide rounded to a scale answers, under what this reading holds of the two it was
     * computed from.
     *
     * <p>The same two questions about the divisor as a truncating divide asks, and for the same
     * reasons. What is said under them depends on whether the scale reads as a number.
     *
     * <p>With one, the answer lies between the two points of that scale's grid the exact quotient
     * lies between, whichever way the call rounds ({@link Intervals#roundedQuotient}) — and the grid
     * is the one the run time will use, which is why a scale no {@code int} holds is no scale here:
     * the run time takes a scale it cannot receive unchanged as no scale either and answers nothing
     * at it (spec §stdlib-decimal), so there is no quotient for a rule to be about.
     *
     * <p>With none, the side of nought is still the same. Rounding to a grid never crosses zero — a
     * quotient at or above nought lands on a grid point at or above nought at every scale — so which
     * side it is on follows from the operands and not from where the grid is. Read off the grid at
     * scale nought, since which side that answer is on is the side every other scale answers too.
     */
    private static Says rounded(FactSubject atom, Derivation.RoundedQuotient rounded,
                                NumericDomain<FactSubject> base, Terms terms,
                                Memo done, Set<FactSubject> deriving, ContextMultiplicity copies) {
        Bounds divisor = divisorOf(rounded.divisor(), rounded.divisorExtent(), base, terms, done,
                deriving, copies);
        if (divisor == null) {
            return Says.NOTHING;
        }
        Bounds numerator = boundsOf(rounded.numerator(), base, terms, done, deriving, copies);
        Integer places = placesOf(boundsOf(rounded.scale(), base, terms, done, deriving, copies),
                terms.policy());
        Bounds answered = Intervals.roundedQuotient(numerator, divisor,
                places == null ? 0 : places);
        if (places != null) {
            return projected(atom, answered, terms);
        }
        // The grid is not one this reading lays out, so where the quotient lies is not stated and
        // an empty answer here would be that and not an operation answering nothing.
        List<Fact> facts = new ArrayList<>();
        if (answered.liesWithin(AT_OR_ABOVE_NOUGHT)) {
            facts.add(new NumericConstraint(LinearForm.atom(atom), Rel.GE));
        }
        if (answered.liesWithin(AT_OR_BELOW_NOUGHT)) {
            facts.add(new NumericConstraint(LinearForm.atom(atom), Rel.LE));
        }
        return new Says.These(List.copyOf(facts));
    }

    /**
     * The scale as the run time takes it, or null where this reading does not hold the argument to
     * one such number.
     *
     * <p>One number, which is a range holding a single value and reaching both of its ends. A scale
     * the reading leaves anywhere else is a grid this cannot name — the answer lands on one grid and
     * a rule stated over two of them is a rule about neither.
     *
     * <p>And a number the run time can receive as the number it is. A scale is an {@code Int}, which
     * is 64 bits, and what a divide is given is 32; a scale outside those aborts rather than being
     * narrowed (spec §stdlib-decimal), so a division at one produces no value and there is nothing
     * for a range to hold. This is the same question the run time asks and not a reading of what the
     * backend happens to emit: the specification states the range, and the compiler and the run time
     * answer it separately — a reading that called into the run time would be a reading whose
     * soundness depended on which backend was linked. The two are held together by a test over the
     * ends rather than by shared code.
     *
     * <p>And a grid this reading will lay out, which is a third question and not a sharpening of the
     * second. What the run time takes is what the language says; what a reading can afford to name
     * is settled by the compilation ({@link ReadingPolicy#laysOutAGridAt}) — a scale of a million
     * places is a number a megabyte wide at every corner of the divide. Asked only the first two,
     * what a reading costs would be the source's to decide.
     *
     * <p>What none of them asks is whether the division at that scale has an answer. A scale of
     * {@code 2147483647} is received exactly and still leaves no quotient a {@code Decimal} holds,
     * which the run time reports as an abort of that operation (spec §stdlib-decimal). A range
     * stated here is a range over the values the operation produced, and a call that produces none
     * leaves it nothing to be wrong about — the same reading a divide that aborts already gets
     * (spec §invariant-discharge-arithmetic).
     */
    private static Integer placesOf(Bounds scale, ReadingPolicy policy) {
        Endpoint low = scale.min();
        Endpoint high = scale.max();
        if (low == null || high == null || !low.inclusive() || !high.inclusive()
                || Count.number(low.at()).compareTo(high.at()) != 0) {
            return null;
        }
        Integer places = ScaleRange.receivedUnchanged(Count.number(low.at()).at());
        if (places == null) {
            return null;
        }
        return policy.laysOutAGridAt(places) ? places : null;
    }

    /**
     * How far from nought the divisor can be, or null where this reading leaves it no such number.
     *
     * <p>The further of the two ends, since what is left is smaller than the divisor it was divided
     * by and the divisor may be any value the reading admits. An end the range does not reach is
     * read as it stands: a divisor short of a number is short of it, and what is left is smaller
     * still.
     */
    private static BigDecimal noFurtherFromNoughtThan(Bounds divisor) {
        if (divisor.min() == null || divisor.max() == null) {
            return null;
        }
        return Count.number(divisor.min().at()).at().abs()
                .max(Count.number(divisor.max().at()).at().abs());
    }

    /** The one number this reading holds {@code bounds} to, or null where it holds it to more than
     * one. What a form the domain carries needs: a coefficient is a number and not a range. */
    private static BigDecimal theOneValueOf(Bounds bounds) {
        if (bounds.min() == null || bounds.max() == null
                || !bounds.min().inclusive() || !bounds.max().inclusive()
                || Count.number(bounds.min().at()).compareTo(bounds.max().at()) != 0) {
            return null;
        }
        return Count.number(bounds.min().at()).at();
    }

    /** What the operator divided by, or null where this rule has no divisor to fire on — see
     * {@link #quotient}. */
    private static Bounds divisorOf(LinearForm<FactSubject> form, Bounds extent,
                                    NumericDomain<FactSubject> base, Terms terms,
                                    Memo done, Set<FactSubject> deriving, ContextMultiplicity copies) {
        Bounds divisor = boundsOf(form, base, terms, done, deriving, copies).meet(extent);
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
                                   Memo done, Set<FactSubject> deriving, ContextMultiplicity copies) {
        NumericDomain<FactSubject> with = base;
        for (FactSubject atom : form.coefs().keySet()) {
            if (recorded(terms, atom)) {
                with = taking(with, derive(atom, base, terms, done, deriving, copies), terms);
            }
        }
        return with.boundsOf(form);
    }

    /** {@code d} with every one of {@code facts} taken as holding, each through the door it names.
     * An end a range does not reach is asserted as the strict comparison it is, which is what the
     * domain reads a range's ends as. */
    private static NumericDomain<FactSubject> taking(NumericDomain<FactSubject> d, Says said,
                                                     Terms terms) {
        NumericDomain<FactSubject> out = d;
        for (Fact fact : said.facts()) {
            out = switch (fact) {
                case Fact.Between(FactSubject atom, Bounds bounds) ->
                        out.assuming(atom, bounds, terms.kindsOf(LinearForm.atom(atom)));
                case NumericConstraint(LinearForm<FactSubject> form, Rel rel) ->
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
