package souther.compiler.check;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.Intervals;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.Bounds;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collection;
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
        ReadingDomain reading = readingOf(base, terms, asked);
        Memo derived = new Memo();
        if (terms.knowsAnything() && !reading.isBottom()) {
            Set<FactSubject> from = new LinkedHashSet<>(asked);
            from.addAll(base.atomsSpokenOf());
            for (FactSubject atom : toDerive(terms, from)) {
                derive(atom, reading, terms, derived, Deriving.nothingYet(),
                        ContextMultiplicity.ofOneReading());
            }
        }
        derived.watched();
        ReadingDomain out = reading;
        for (List<Fact> facts : derived.answered.values()) {
            out = out.taking(facts, terms);
        }
        return out.domain();
    }

    /**
     * A domain a recipe may be read against: one with what every value it can reach carries taken as
     * holding.
     *
     * <p>The first of the two stages, held as a type so that the second cannot be run without it.
     * What a value carries is true in every domain — a size is never negative whatever a guard said —
     * so it is not something a recipe derives but something the reading starts from, and a reading
     * that started without it answered about a fold's step as though nothing were known of anything
     * the step named (#988).
     *
     * <p>A class with a constructor of its own, and not a record. A record's canonical constructor is
     * as accessible as the record is, and this one has to be seen by {@link InductiveBounds} — so as
     * a record, any reader in this package could wrap a raw domain and reach {@link #derive} with a
     * reading that had skipped the first stage, which is the thing the type is here to stop. Written
     * this way the stage is not a rule to follow: it is the only way to hold one of these. Every
     * operation that moves a reading along is here for the same reason.
     *
     * <p>What it reaches is not kept beside it. An arm's statements and a candidate for an
     * accumulator are relations over atoms the recipe already declared it reads from
     * ({@link AtomKnowledge.Computation#formsRead}), so every value a reading moved along this way
     * can reach was spoken for when it was made — and a set carried through the moves would be a
     * second writing of that, read by nobody and true only for as long as nobody changed a move.
     */
    static final class ReadingDomain {

        private final NumericDomain<FactSubject> domain;

        private ReadingDomain(NumericDomain<FactSubject> domain) {
            this.domain = domain;
        }

        private NumericDomain<FactSubject> domain() {
            return domain;
        }

        boolean isBottom() {
            return domain.isBottom();
        }

        Bounds boundsOf(LinearForm<FactSubject> form) {
            return domain.boundsOf(form);
        }

        ReadingDomain assume(LinearForm<FactSubject> form, Rel rel, Map<FactSubject, Granularity> kinds) {
            return new ReadingDomain(domain.assume(form, rel, kinds));
        }

        ReadingDomain assuming(FactSubject atom, Bounds bounds, Map<FactSubject, Granularity> kinds) {
            return new ReadingDomain(domain.assuming(atom, bounds, kinds));
        }

        /** This, with what a walk's step is handed taken as holding. */
        ReadingDomain taking(StepInputFacts inputs) {
            return new ReadingDomain(inputs.taking(domain));
        }

        /** This, with every one of {@code facts} taken as holding, each through the door it names.
         * An end a range does not reach is asserted as the strict comparison it is, which is what
         * the domain reads a range's ends as. */
        ReadingDomain taking(List<Fact> facts, Terms terms) {
            NumericDomain<FactSubject> out = domain;
            for (Fact fact : facts) {
                out = switch (fact) {
                    case Fact.Between(FactSubject atom, Bounds bounds) ->
                            out.assuming(atom, bounds, terms.kindsOf(LinearForm.atom(atom)));
                    case NumericConstraint(LinearForm<FactSubject> form, Rel rel) ->
                            out.assume(form, rel, terms.kindsOf(form));
                };
            }
            return new ReadingDomain(out);
        }
    }

    /**
     * {@code base} as a reading: what every atom it can reach carries, taken as holding.
     *
     * <p>What it can reach is the closure over both kinds of edge ({@link Terms#reached}), because
     * an intrinsic relation is as much a reason to reach a value as a recipe reading from one: a
     * container's size is no greater than the size of what it was built from, and the second of
     * those has to be in the reading for the first to say anything.
     *
     * <p>Not an inference and not a round. What is taken in holds of the values whatever any of it
     * comes to, so nothing here is read back to reach anything else — the closure is over what the
     * naming recorded, and it is walked once.
     */
    static ReadingDomain readingOf(NumericDomain<FactSubject> base, Terms terms,
                                   Set<FactSubject> asked) {
        Set<FactSubject> from = new LinkedHashSet<>(asked);
        from.addAll(base.atomsSpokenOf());
        NumericDomain<FactSubject> out = base;
        for (FactSubject atom : terms.reachedFrom(from)) {
            for (NumericConstraint fact : terms.knowledgeOf(atom).intrinsic()) {
                out = out.assume(fact.form(), fact.rel(), terms.kindsOf(fact.form()));
            }
        }
        return new ReadingDomain(out);
    }

    /** Whether {@code atom} was recorded as anything this can derive from, which is a computation
     * and not what the value carries: what it carries is already in the reading, and putting it
     * through a derivation would make a value nothing computes count as a recipe evaluated. */
    private static boolean recorded(Terms terms, FactSubject atom) {
        return !(terms.knowledgeOf(atom).computation() instanceof AtomKnowledge.Computation.None);
    }

    /**
     * The atoms a reading asked about {@code asked} is to derive from: everything reading those
     * reaches that was recorded as computed.
     *
     * <p>One answer, and it was two. The reading a question is asked in answered it from the domain,
     * and reading a form answered it from the atoms the form names — so a value the reading reached
     * but the form did not name was a recipe nobody put through. That is not a narrowing at the
     * edges: what a value carries relates it to other values, and {@code Decimal.toInt} carries that
     * its answer is within one of what it rounded. Read where a clause names it, the thing it
     * rounded is in the domain and is derived; read inside a step, the step names the answer and not
     * what it rounded, and a product there was a value nothing bounded whatever its factors were.
     * The same divergence as #988 and along the other edge of the same graph.
     *
     * <p>So it is asked once, and of what the values asked about carry
     * ({@link Terms#carriedReachFrom}) rather than of a form's own atoms. What a caller supplies is
     * only what it asked about.
     *
     * <p>That reaching and not the whole of one. A value under a recipe is reached too, and it is
     * not wanted here: putting a recipe through a reading reads its operands as part of reading it,
     * and asking for them here as well is asking for the same work once per arm a reading is copied
     * into — which is a cost that compounds with nesting where the recipes' own reading does not
     * ({@link ContextMultiplicity}). What only a relation names has no such second route, which is
     * why it is this reaching that belongs here.
     */
    private static Set<FactSubject> toDerive(Terms terms, Collection<FactSubject> asked) {
        Set<FactSubject> out = new LinkedHashSet<>();
        for (FactSubject atom : terms.carriedReachFrom(asked)) {
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

        private final Map<FactSubject, List<Fact>> answered = new LinkedHashMap<>();

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
     * What a reading is in the middle of deriving, which is two questions and was one set.
     *
     * <p>An atom reached again is either this check disagreeing with itself or it is not, and which
     * it is depends on how the reading got back to it. A recipe is recorded over the parts a value
     * was built from and a part is a strictly smaller expression, so a computation that reaches
     * itself is a value the naming built out of itself — the thing {@link AnAtomComputedFromItself}
     * is for. Reading a recipe also reads the values a relation drags in
     * ({@link Terms#carriedReachFrom}), and those carry no such ordering: {@code a} computed from
     * {@code c}, {@code c} carrying a relation about {@code b}, and {@code b} computed from
     * {@code a} is three true statements and no cycle among computations at all.
     *
     * <p>So the two are held apart. {@link #alongComputations} is the chain of recipes the reading
     * is inside, and it begins again wherever the reading steps across to a value only a relation
     * named; {@link #anywhere} is every atom in flight, and it is what stops the walk going round.
     * Written as one set, "is this atom below me on the stack" answered a question about the
     * computation graph, and a ring that closed through a relation was reported as this check
     * having built a value out of itself (#988).
     */
    private static final class Deriving {

        private final Set<FactSubject> alongComputations;
        private final Set<FactSubject> anywhere;

        private Deriving(Set<FactSubject> alongComputations, Set<FactSubject> anywhere) {
            this.alongComputations = alongComputations;
            this.anywhere = anywhere;
        }

        static Deriving nothingYet() {
            return new Deriving(new LinkedHashSet<>(), new LinkedHashSet<>());
        }

        /** The same reading, stepping across to a value a relation named rather than down into what
         * a recipe was computed from. What is in flight carries over — the walk still has to stop —
         * and the chain of recipes starts again, because none of the recipes below this point was
         * reached from the ones above it. */
        Deriving throughWhatAValueCarries() {
            return new Deriving(new LinkedHashSet<>(), anywhere);
        }

        /** Whether deriving {@code atom} now would be a computation reaching itself. */
        boolean computesFromItself(FactSubject atom) {
            return alongComputations.contains(atom);
        }

        /** Whether {@code atom} is being derived somewhere this reading is already inside. */
        boolean isInFlight(FactSubject atom) {
            return anywhere.contains(atom);
        }

        void entering(FactSubject atom) {
            alongComputations.add(atom);
            anywhere.add(atom);
        }

        void left(FactSubject atom) {
            alongComputations.remove(atom);
            anywhere.remove(atom);
        }
    }

    /**
     * What is known of {@code atom}, computed once and remembered.
     *
     * <p>Two ways of arriving at an atom the reading is already inside, and they are not one answer
     * ({@link Deriving}). A computation that reaches itself is refused. A ring that closes only
     * through what a value carries is answered with nothing — a reading that cannot see round it
     * says less, which is what a reading should do, where refusing it would state something false
     * about this check's own naming.
     *
     * <p>What is answered there is not remembered. Nothing is a shorter answer than the one this
     * atom will have once the reading is out of the ring, and filing it would hand that shorter
     * answer to the next reader to ask.
     */
    private static List<Fact> derive(FactSubject atom, ReadingDomain base, Terms terms,
                                     Memo done, Deriving deriving, ContextMultiplicity copies) {
        List<Fact> had = done.answered.get(atom);
        if (had != null) {
            return had;
        }
        if (deriving.computesFromItself(atom)) {
            throw new AnAtomComputedFromItself(atom);
        }
        if (deriving.isInFlight(atom)) {
            return List.of();
        }
        deriving.entering(atom);
        done.evaluating(atom);
        List<Fact> facts = factsFor(atom, base, terms, done, deriving, copies);
        deriving.left(atom);
        done.answered.put(atom, facts);
        return facts;
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
    private static List<Fact> factsFor(FactSubject atom, ReadingDomain base, Terms terms,
                                       Memo done, Deriving deriving, ContextMultiplicity copies) {
        return switch (terms.knowledgeOf(atom).computation()) {
            // What the value carries is not derived. It holds in every reading and is already in
            // this one, so putting it through here would count a value nothing computes as a recipe
            // evaluated and would say a second time what the reading was made with.
            case AtomKnowledge.Computation.None ignored -> List.of();
            case AtomKnowledge.Computation.Reduction(InductiveBounds.Walk walk) ->
                    reduced(atom, walk, base, terms, deriving, copies);
            case AtomKnowledge.Computation.Derived(Derivation recipe) ->
                    recipeFacts(atom, recipe, base, terms, done, deriving, copies);
        };
    }

    /** What a walk answers, proved by checking one step. */
    private static List<Fact> reduced(FactSubject atom, InductiveBounds.Walk walk, ReadingDomain base,
                                      Terms terms, Deriving deriving,
                                      ContextMultiplicity copies) {
        // Each reading of the walk's own forms gets a memo of its own, since each is against a
        // different domain — the caller's, and the caller's with a candidate assumed. What is
        // shared is `deriving`, which is what says an atom was built out of itself, and that is
        // true of a recipe whatever domain it is read in.
        return between(atom, InductiveBounds.provenOf(walk, base, terms, (form, domain) -> {
            Memo memo = new Memo();
            Bounds answer = boundsOf(form, domain, terms, memo, deriving, copies);
            // A reading, and watched as one. What the walk reads is where a step's own recipes
            // are evaluated, so a reading that could not be seen here was the one place the
            // memo could stop holding without anything saying so.
            memo.watched();
            return answer;
        }), terms);
    }

    /** What the arithmetic a recipe records answers, under this reading. */
    private static List<Fact> recipeFacts(FactSubject atom, Derivation of, ReadingDomain base,
                                          Terms terms, Memo done, Deriving deriving,
                                          ContextMultiplicity copies) {
        return switch (of) {
            case Derivation.Product product -> between(atom, Intervals.product(
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
    private static Bounds chosen(Derivation.Chosen chosen, ReadingDomain base,
                                 Terms terms, Memo done, Deriving deriving,
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
            ReadingDomain under = stating(arm, base, terms);
            // An arm whose statements cannot all hold is an arm this choice never answers, so it
            // contributes no values to the span. Spanning with what it would have answered widens
            // the range by an arm that is not there — which is how a value every arm of which is
            // the accumulator stopped being the accumulator.
            if (under.isBottom()) {
                continue;
            }
            out = spanned(out, readingAnArm(arm, under, terms, deriving, inAnArm));
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
    private static ReadingDomain stating(Derivation.Chosen.Arm arm, ReadingDomain base, Terms terms) {
        ReadingDomain under = base;
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
    private static Bounds readingAnArm(Derivation.Chosen.Arm arm, ReadingDomain under,
                                       Terms terms, Deriving deriving,
                                       ContextMultiplicity copies) {
        Memo memo = new Memo();
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
     * <p><b>Where the correction leaves nothing, nothing is stated — and not an empty range.</b> The
     * arithmetic worked out to values the value it is about cannot take, so the operation answers on
     * no input this reading admits, and the operator that would have answered aborts instead. That
     * the path therefore has no execution is a stronger thing than this procedure states: whether an
     * operation aborts at all is settled by the divisor's own type or by a {@code require} (spec
     * §invariant-discharge-arithmetic), and a reading is not where the language takes that on.
     * Asserted as an empty range it would be a contradiction, and a contradictory domain proves
     * every clause there is — which is the same trap a rule with no operands to fire on is kept out
     * of ({@link #quotient}), and here it does not even hold: what a clause is refused by is not the
     * numeric rules alone, so a construction would come out established by the numbers and refused
     * by the predicates at once, which is the check disagreeing with itself.
     *
     * <p>So the value is one nothing is known of, and a construction over it is owed its clause as
     * it is owed over any other such value. What is fixed is that nothing is known of it <em>as a
     * number no {@code Int} is</em> — which is what a reading refused a construction by.
     */
    private static List<Fact> between(FactSubject atom, Bounds bounds, Terms terms) {
        Bounds held = heldToWhatItCanBe(atom, bounds, terms);
        return held.holdsAValue() ? List.of(new Fact.Between(atom, held)) : List.of();
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
    private static List<Fact> quotient(FactSubject atom, Derivation.TruncatingQuotient quotient,
                                       ReadingDomain base, Terms terms,
                                       Memo done, Deriving deriving, ContextMultiplicity copies) {
        Bounds divisor = divisorOf(quotient.divisor(), quotient.divisorExtent(), base, terms, done,
                deriving, copies);
        if (divisor == null) {
            return List.of();
        }
        Bounds numerator = boundsOf(quotient.numerator(), base, terms, done, deriving, copies);
        Bounds held = heldToWhatItCanBe(atom,
                Intervals.truncatingQuotient(numerator, divisor), terms);
        // Nothing at all, and not the halves that do not mention the range. What is left of a
        // dividend relates the quotient to it, so a reading that dropped where the quotient lies and
        // kept that relation would put the quotient back where the arithmetic had it — a number no
        // `Int` is, reached the long way round.
        if (!held.holdsAValue()) {
            return List.of();
        }
        List<Fact> facts = new ArrayList<>();
        facts.add(new Fact.Between(atom, held));
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
                                        ReadingDomain base, Terms terms,
                                        Memo done, Deriving deriving, ContextMultiplicity copies) {
        Bounds divisor = divisorOf(remainder.divisor(), remainder.divisorExtent(), base, terms, done,
                deriving, copies);
        if (divisor == null) {
            return List.of();
        }
        return leftOver(LinearForm.atom(atom), divisor,
                boundsOf(remainder.numerator(), base, terms, done, deriving, copies));
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
    private static List<Fact> rounded(FactSubject atom, Derivation.RoundedQuotient rounded,
                                      ReadingDomain base, Terms terms,
                                      Memo done, Deriving deriving, ContextMultiplicity copies) {
        Bounds divisor = divisorOf(rounded.divisor(), rounded.divisorExtent(), base, terms, done,
                deriving, copies);
        if (divisor == null) {
            return List.of();
        }
        Bounds numerator = boundsOf(rounded.numerator(), base, terms, done, deriving, copies);
        Integer places = placesOf(boundsOf(rounded.scale(), base, terms, done, deriving, copies),
                terms.policy());
        Bounds answered = Intervals.roundedQuotient(numerator, divisor,
                places == null ? 0 : places);
        if (places != null) {
            return between(atom, answered, terms);
        }
        List<Fact> facts = new ArrayList<>();
        if (answered.liesWithin(AT_OR_ABOVE_NOUGHT)) {
            facts.add(new NumericConstraint(LinearForm.atom(atom), Rel.GE));
        }
        if (answered.liesWithin(AT_OR_BELOW_NOUGHT)) {
            facts.add(new NumericConstraint(LinearForm.atom(atom), Rel.LE));
        }
        return facts;
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
                                    ReadingDomain base, Terms terms,
                                    Memo done, Deriving deriving, ContextMultiplicity copies) {
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
    private static Bounds boundsOf(LinearForm<FactSubject> form, ReadingDomain base, Terms terms,
                                   Memo done, Deriving deriving, ContextMultiplicity copies) {
        ReadingDomain with = base;
        for (FactSubject atom : toDerive(terms, form.coefs().keySet())) {
            // Which of the two edges this atom was reached by is the whole of what the refusal below
            // turns on, and it is known here and nowhere else: an atom the form names is what this
            // recipe was computed from, and every other one is a value some relation dragged in.
            Deriving how = form.coefs().containsKey(atom)
                    ? deriving : deriving.throughWhatAValueCarries();
            with = with.taking(derive(atom, base, terms, done, how, copies), terms);
        }
        return with.boundsOf(form);
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
