package souther.compiler.check;

import souther.compiler.types.BinOp;
import souther.compiler.check.Combinators.Handed;
import souther.compiler.check.DischargeRules.Cardinality;
import souther.compiler.check.DischargeRules.Carrying;
import souther.compiler.check.DischargeRules.Projection;
import souther.compiler.check.DischargeRules.Shape;
import souther.compiler.check.DischargeRules.Source;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collection;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * How a predicate is read: what a clause owes where a value is built, what a guard settles where one
 * is written, and the keys by which the two meet.
 *
 * <p>One language, read in two directions. An invariant clause and a guard are the same kind of
 * expression, and a clause is discharged exactly when a guard has stated what it owes — so what a
 * clause owes and what a guard establishes come out of one reading, differing only in which way it
 * runs. Written apart, the two would drift, and every drift is a clause an author guarded and the
 * check still reported.
 *
 * <p>Nothing here decides anything about a program. It answers what is owed and what is known, and
 * the walk that threads {@link Known} is what asks.
 */
final class Predicates {

    private final Terms terms;

    Predicates(Terms terms) {
        this.terms = terms;
    }

    /** The relations known of every element of {@code container}: those stated of it as written, and
     * those stated of a container it was built from that travel every construction in between. */
    List<Quantified> elementRelations(Core container, Known k, Denotations at) {
        List<Quantified> found = new ArrayList<>();
        Set<Shape> crossed = EnumSet.noneOf(Shape.class);
        Core source = container;
        while (true) {
            FactSubject key = terms.subjectOf(source, at);
            if (key != null) {
                for (Quantified q : k.quantified()) {
                    if (key.equals(q.container()) && q.through().containsAll(crossed)) {
                        found.add(q);
                    }
                }
            }
            if (!(source instanceof Core.PreservedCall call)) {
                return found;
            }
            Source built = DischargeRules.builtFrom(call);
            if (built == null) {
                return found;
            }
            crossed.add(built.shape());
            source = built.container();
        }
    }

    /** What {@code q} says of the value at {@code element}, taken into {@code k}. The predicate is
     * read again with the quantifier's own parameter standing for that element — the same reading the
     * seeding does of a type's invariant, over the clause a quantifier holds. A relation the
     * predicate in turn states of a container is recorded, so a container of containers reaches its
     * innermost element. */
    Known instantiate(Quantified q, Core element, Known k, Denotations at) {
        Core stated = Clauses.substituted(q.predicate().body(),
                Map.of(q.predicate().params().get(0).binding(), element));
        List<Quantified> nested = new ArrayList<>();
        quantifiedBy(stated, at, true, nested);
        // A quantifier is recorded by a guard and by a type's invariant alike, and carries no record
        // of which recorded it, so what it gives an element is taken as the path's. That is the
        // weaker of the two readings: a violation it decides is reported as one the values alone did
        // not decide, which holds either way. It is why nothing downstream says a guard decided it.
        return assume(obligations(stated, k, at, false), k, Known.Held.ON_THE_PATH).and(nested);
    }

    /** What {@code e}, asserted with polarity {@code positive}, says of every element of a container.
     * Mirrors {@link #obligations}: a conjunction states each of its sides, and a negation flips the
     * polarity. Only a stated quantifier is recorded — denying one says some element fails the
     * predicate, and which one is not something this check can name. */
    void quantifiedBy(Core raw, Denotations at, boolean positive, List<Quantified> out) {
        Core e = Conditions.asSizeComparison(raw);
        if (e instanceof Core.Binary b && b.op() == BinOp.AND && positive) {
            quantifiedBy(b.left(), at, true, out);
            quantifiedBy(b.right(), at, true, out);
            return;
        }
        Core under = Conditions.negated(e);
        if (under != null) {
            quantifiedBy(under, at, !positive, out);
            return;
        }
        if (!positive || !(e instanceof Core.PreservedCall call)
                || !DischargeRules.isQuantifier(call.operation())) {
            return;
        }
        Handed over = Combinators.handedTo(call, at);
        Carrying carried = DischargeRules.carried(call);
        if (over == null || carried == null || over.step().params().size() != 1) {
            return;
        }
        // The container is the carrying rule's, which is the one argument this predicate is about.
        // What the operation hands its closure answers the same question about the same argument, and
        // is asked here only for the closure.
        FactSubject container = terms.subjectOf(carried.container(), at);
        if (container == null) {
            return;
        }
        out.add(new Quantified(container, carried.through(), over.step()));
    }

    /** Whether {@code e} is, or names, one of {@code values}. */
    static boolean names(Core e, Set<Core> values) {
        if (values.contains(e)) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(e, child -> found[0] = found[0] || names(child, values));
        return found[0];
    }

    /**
     * A predicate stated of a term. {@code keys} is the term as written first, then each container it
     * was built from by a construction that carries the predicate — any one of them settled is this
     * clause established. Refuting reads only the first: denying a predicate of a list says nothing
     * about a list built from it. {@code positive} is false for a clause written under a negation,
     * and such a clause carries nowhere, since the implication runs the other way.
     */
    record Fact(List<FactSubject> keys, boolean positive) {

        boolean entailedBy(PredicateFacts<FactSubject> facts) {
            for (FactSubject key : keys) {
                if (facts.entails(key, positive)) {
                    return true;
                }
            }
            return false;
        }

        boolean refutedBy(PredicateFacts<FactSubject> facts) {
            return facts.refutes(keys.get(0), positive);
        }
    }

    /**
     * One case of a clause read over an operation that answers one of the values it was given: the
     * clause with that value standing where the call did, and what holds of the arguments there.
     *
     * @param kinds how the values of every atom either of them names are spaced, so that a case can
     *              be taken into a domain without asking anything further of the caller
     */
    record Case(NumericConstraint numeric, List<NumericConstraint> given, Map<FactSubject, Granularity> kinds) {

        /**
         * Every atom this case is decided by.
         *
         * <p>Read off {@code kinds}, which is where the atoms of this case are registered as its
         * forms are built — the substituted clause, the equality saying the call answered this
         * argument, and each condition on the arguments. A reader listing those three would be a
         * second answer to keep in step with the building, and the one that would fall behind: what
         * a condition names and never answers is an atom of this case all the same, and today no
         * operation in the table has such an argument.
         */
        Set<FactSubject> atomsItIsDecidedBy() {
            return kinds.keySet();
        }

        /** {@code d} with this case's conditions on the arguments taken as holding. */
        private NumericDomain<FactSubject> in(NumericDomain<FactSubject> d) {
            NumericDomain<FactSubject> out = d;
            for (NumericConstraint one : given) {
                out = out.assume(one.form(), one.rel(), kinds);
            }
            return out;
        }
    }

    /**
     * A clause read as the cases the operation standing under it is defined in.
     *
     * <p>What a case holds is its condition on the arguments and the equality saying the call
     * answered that argument, and it is reached where those and what is known here can hold at once.
     * The equality is what ties the two readings of one value together: without it a guard written
     * about the call would stand outside every case, and this would answer about a value the rest of
     * the check is talking about separately.
     *
     * <p>So, over the cases that are reached: all of them proving the clause is the clause
     * established, all of them refuting it is the clause refused, and anything else is unsettled.
     * The cases are exhaustive ({@link DischargeRules.Choices}), which is what makes the first two
     * statements about the result rather than about a case of it.
     *
     * <p>No case reached is not the clause established. It says the guards cannot all hold, and a
     * value the program never builds establishes nothing — while the reading that takes the call as
     * an unknown still has whatever a guard said about it, and answers there. Calling it vacuously
     * proven would have this establishing a clause that reading refuses, which is the check
     * disagreeing with itself about one value rather than an answer. The same holds when the cases
     * come to be multiplied out.
     *
     * <p>One operation to a clause. Where a clause names two of them the cases multiply, and what
     * that costs is a decision this does not have to make yet — such a clause is read as it stands,
     * which proves less and states nothing false.
     */
    record Piecewise(List<Case> cases) {

        /** Every atom any case of this is decided by. A case that is never reached is one the
         * conditions rule out, and which those are is what the domain answers — so every case is
         * counted here, including the ones a reading will drop. */
        Set<FactSubject> atomsItIsDecidedBy() {
            Set<FactSubject> out = new LinkedHashSet<>();
            for (Case one : cases) {
                out.addAll(one.atomsItIsDecidedBy());
            }
            return out;
        }

        boolean entailedBy(NumericDomain<FactSubject> d) {
            boolean reached = false;
            for (Case one : cases) {
                NumericDomain<FactSubject> here = one.in(d);
                if (here.isBottom()) {
                    continue;
                }
                if (!here.entails(one.numeric().form(), one.numeric().rel())) {
                    return false;
                }
                reached = true;
            }
            return reached;
        }

        boolean refutedBy(NumericDomain<FactSubject> d) {
            boolean reached = false;
            for (Case one : cases) {
                NumericDomain<FactSubject> here = one.in(d);
                if (here.isBottom()) {
                    continue;
                }
                if (!here.refutes(one.numeric().form(), one.numeric().rel())) {
                    return false;
                }
                reached = true;
            }
            return reached;
        }
    }

    /** A clause that cannot hold, said in the language the domain reads: {@code -1 >= 0}. */
    static final Clause VIOLATED = new Clause(
            new NumericConstraint(LinearForm.constant(BigDecimal.ONE.negate()), Rel.GE), null, List.of(),
            null);

    /**
     * One clause of an invariant, and the two ways it can come out: a relation for the domain to
     * prove, and the key a guard restating it settles. Either may be absent, and where both are
     * present either one discharging the clause is enough — a guard is written one way and a clause
     * another, and which of the two routes carries it is not the author's concern.
     */
    record Clause(NumericConstraint numeric, Fact fact, List<NumericConstraint> known, Piecewise piecewise) {

        /**
         * Every atom a numeric domain could decide this clause differently by.
         *
         * <p>The question a reading asks before it decides what to prove about the arithmetic it
         * cannot carry: a bound derived for an atom no clause is decided by, and that the domain
         * does not speak of either, changes nothing here ({@link NumericDomain#atomsSpokenOf}).
         *
         * <p>What a guard settled by name is not this. {@link Fact} is answered by
         * {@link PredicateFacts} and never by the domain, so its keys are not atoms a bound could
         * reach — and counting them would put terms into a derivation's roots that no arithmetic is
         * read off.
         *
         * <p>{@code known} is here though a reading that takes it as holding first would reach those
         * atoms anyway. This says what the clause is decided by, which is a fact about the clause;
         * that a caller happens to have put the same atoms into its domain a line earlier is a fact
         * about the caller, and answering by what some caller does is how the answer comes to be
         * wrong for the next one.
         */
        Set<FactSubject> atomsItIsDecidedBy() {
            Set<FactSubject> out = new LinkedHashSet<>();
            if (numeric != null) {
                out.addAll(numeric.atoms());
            }
            for (NumericConstraint one : known) {
                out.addAll(one.atoms());
            }
            if (piecewise != null) {
                out.addAll(piecewise.atomsItIsDecidedBy());
            }
            return out;
        }

        boolean dischargedBy(NumericDomain<FactSubject> d, PredicateFacts<FactSubject> facts) {
            return numeric != null && d.entails(numeric.form(), numeric.rel())
                    || fact != null && fact.entailedBy(facts)
                    || piecewise != null && !decidedAsWritten(d, facts) && piecewise.entailedBy(d);
        }

        boolean refutedBy(NumericDomain<FactSubject> d, PredicateFacts<FactSubject> facts) {
            return numeric != null && d.refutes(numeric.form(), numeric.rel())
                    || fact != null && fact.refutedBy(facts)
                    || piecewise != null && !decidedAsWritten(d, facts) && piecewise.refutedBy(d);
        }

        /**
         * Whether the clause as written already came out one way or the other.
         *
         * <p>The cases are asked only where it did not. Both readings are sound, so they can differ
         * only where the path cannot be taken — the guards contradict, and each is answering about a
         * value the program never builds. Where that is visible in the guards it is said there
         * ({@link #noCaseSatisfies}) and neither reading is reached; where it is not, this is what
         * keeps one clause from coming out established and refused at once, which is a check
         * contradicting itself rather than an answer. What the cases are for is a clause the reading
         * that takes the call as an unknown cannot settle, and that is untouched.
         */
        private boolean decidedAsWritten(NumericDomain<FactSubject> d, PredicateFacts<FactSubject> facts) {
            return numeric != null
                    && (d.entails(numeric.form(), numeric.rel())
                            || d.refutes(numeric.form(), numeric.rel()))
                    || fact != null && (fact.entailedBy(facts) || fact.refutedBy(facts));
        }
    }

    /**
     * What a clause owes: its parts in the order they were read, and what the clause itself folded
     * to.
     *
     * <p>One list, with what was carried and what was not as two shapes in it. A conjunction can be
     * both at once — one conjunct discharged and the next unreadable — and a list of what was
     * carried beside one node for what was not says the invariant was proven where half of it was
     * never read, keeps only the first of two unreadable parts, and loses the order the author wrote
     * them in. All three go away by making them variants of one sequence.
     *
     * <p>{@code folded} is about the clause and not about a part of it. A conjunct folding the way
     * it is read owes nothing and contributes no part; the clause folds only as all of it does
     * ({@link Fold#and}), so this is beside the parts rather than one of them.
     *
     * @param parts  what the clause asks of a construction, each carried or not
     * @param folded whether the clause came out one way on its own, before any construction was
     *               looked at
     */
    record Owed(List<Part> parts, Fold folded) {

        /** Nothing is owed because the clause came out one way or the other on its own. */
        static Owed decided(boolean holds) {
            return new Owed(List.of(), holds ? Fold.HOLDS : Fold.FAILS);
        }

        /** One part of the clause this could make nothing of, which is {@code where}. */
        static Owed unreadable(Core where) {
            return new Owed(List.of(new Part.Unread(where)), Fold.NOT_DECIDED);
        }

        static Owed of(Clause clause) {
            return new Owed(List.of(new Part.Carried(clause)), Fold.NOT_DECIDED);
        }

        /** Whether a part of it names something the check cannot read here. */
        boolean unreadable() {
            for (Part each : parts) {
                if (each instanceof Part.Unread) {
                    return true;
                }
            }
            return false;
        }

        /** The same, having come out one way on its own as well. Said beside what it owes rather
         *  than instead of it: which of the two a caller acts on is the caller's, and a reading that
         *  answered only one of them decided that for every caller there will ever be. */
        Owed alsoFolded(Fold fold) {
            return fold == Fold.NOT_DECIDED ? this : new Owed(parts, fold);
        }

        /** Both conjuncts of one clause: every part either owes, in the order they were read, and
         *  folded only as both of them together fold. */
        Owed and(Owed other) {
            List<Part> both = new ArrayList<>(parts);
            both.addAll(other.parts);
            return new Owed(List.copyOf(both), folded.and(other.folded));
        }
    }

    /**
     * One thing a clause asks of a construction.
     *
     * <p>Carried or not, and the difference is the shape rather than a field beside a list. Held as
     * a list of what was carried with one node for what was not, a clause with two parts outside the
     * fragment kept the first and dropped the second — so an author acting on what they were shown
     * would fix one and find the construction still refused. The two also interleave, and a reader
     * showing them in the order they were written needs them in one list to do it.
     */
    sealed interface Part {

        /** The check carried it into a form a guard can be held against. */
        record Carried(Clause clause) implements Part {

            public Carried {
                if (clause == null) {
                    throw new IllegalArgumentException("a part that was carried has a form");
                }
            }
        }

        /**
         * The check made nothing of it, and {@code at} is the part it stopped on.
         *
         * <p>The node and not a word for it. Whoever reads this wants to say what in the clause was
         * not read, and working that out from the clause afterwards is a second walk that can come
         * back with a different answer from the one that gave up — which is how a clause with
         * nothing wrong in it came to be described as naming a term the check cannot name.
         */
        record Unread(Core at) implements Part {

            public Unread {
                if (at == null) {
                    throw new IllegalArgumentException("a part nothing was made of is somewhere");
                }
            }
        }
    }

    /**
     * Whether a clause came out one way or the other before any construction was looked at.
     *
     * <p>Read here, off the expression this walk normalizes and reads, rather than off the one an
     * author wrote. {@code Int.compare(1, 2) >= 0} is a call until {@link #asOrderComparison} makes
     * it {@code 1 >= 2}, so a reader folding the written form first sees a call and the fold that
     * matters happens in here.
     */
    enum Fold {

        /** It reads something the construction decides. */
        NOT_DECIDED,

        /** It holds of every value, so no guard is asked for it. */
        HOLDS,

        /** It holds of none, so no guard establishes it. */
        FAILS;

        /** Both conjuncts: failing where either fails, holding only where both hold. */
        Fold and(Fold other) {
            if (this == FAILS || other == FAILS) {
                return FAILS;
            }
            return this == HOLDS && other == HOLDS ? HOLDS : NOT_DECIDED;
        }
    }

    /** What {@code inv} owes, where {@code decidesFalse} says a clause folding to the other answer
     * than it is read with is this check's to report. A newtype's constant construction is checked
     * elsewhere, and that check names the clause that failed rather than only saying one did, so it
     * is left to say it. */
    Owed obligations(Core inv, Known k, Denotations at, boolean decidesFalse) {
        return obligations(inv, k, at, Set.of(), true, decidesFalse, Read.AN_ASSUMPTION, null);
    }

    /**
     * The same, telling {@code per} what each part of the clause owed as it is read.
     *
     * <p>A conjunction is read a conjunct at a time, and what each conjunct came to is this
     * reading's own answer about that conjunct. Handed over here rather than asked again afterwards:
     * a second reading of a part is a second reader, and the two agree only for as long as nobody
     * changes one of them.
     */
    Owed obligations(Core inv, Known k, Denotations at, boolean decidesFalse, PerPart per) {
        return obligations(inv, k, at, Set.of(), true, decidesFalse, Read.AN_ASSUMPTION, per);
    }

    /** Told what one part of a clause owed, keyed by the part it was read from. */
    interface PerPart {
        void read(Core part, Owed owed);
    }

    /**
     * Whether a clause is being read as something that makes knowledge or as something that spends
     * it. Not a direction of travel: the two read one expression through one reader, which is what
     * keeps them from drifting, and this is the single thing they cannot share.
     *
     * <p>An assumption produces. A guard holds because the branch was taken, an {@code ensures}
     * holds because the callee established it, and an invariant holds because the value was built
     * through a checked constructor — none of them needs anything to have been said about the value
     * beforehand, and each is how something first comes to be said about it.
     *
     * <p>An obligation spends. It asks the author to account for a value, and asking that about a
     * value nothing has ever said anything of is asking for something no guard they could write
     * would settle; the run-time check stands for such a clause instead.
     *
     * <p>Requiring an assumption to spend what it produces is the circle it looks like: to be spoken
     * of, a value would have to already be spoken of. It is not a theoretical worry — written that
     * way, a declaration that refutes a construction stopped refusing it, because the declaration was
     * turned away for want of the knowledge it was carrying.
     */
    enum Read {
        /** Knowledge being made: a guard, an invariant, a declared guarantee. */
        AN_ASSUMPTION,
        /** Knowledge being spent: a clause this construction has to account for. */
        AN_OBLIGATION
    }

    /** The same, where {@code unnamed} holds the values the site hands over that no clause may be
     * read against. */
    Owed obligations(Core inv, Known k, Denotations at, Set<Core> unnamed,
                     boolean decidesFalse) {
        return obligations(inv, k, at, unnamed, true, decidesFalse, Read.AN_OBLIGATION, null);
    }

    /**
     * A clause is read as the comparison it states, and where an order call states one there are two
     * readings of it: the order the call decides, and the bound on the sign that decides it. Which of
     * them this construction can be read against is not known until it is read — a date the check can
     * name is one thing, and the date a day after it is another — so the one that answers is the one
     * taken. Reading a predicate never takes a reading away.
     */
    private Owed obligations(Core rawInv, Known k, Denotations at, Set<Core> unnamed,
                             boolean positive, boolean decidesFalse, Read way, PerPart per) {
        Core sized = Conditions.asSizeComparison(rawInv);
        Core ordered = Conditions.asOrderComparison(terms, sized, at);
        Owed read = read(ordered, k, at, unnamed, positive, decidesFalse, way, per);
        Owed out = ordered != sized && read.unreadable()
                ? read(sized, k, at, unnamed, positive, decidesFalse, way, per) : read;
        if (per != null) {
            // Keyed by the part as it was handed in, which is the node a reader of this walk holds.
            // What it was rewritten to on the way is this reading's business.
            per.read(rawInv, out);
        }
        return out;
    }

    /** What {@code inv} owes, read as it stands. Its parts are read through {@link #obligations},
     * which is where each of them is taken as the comparison it states. */
    private Owed read(Core inv, Known k, Denotations at, Set<Core> unnamed,
                      boolean positive, boolean decidesFalse, Read way, PerPart per) {
        if (inv instanceof Core.Binary b && b.op() == BinOp.AND && positive) {
            // Each conjunct on its own: an invariant is a set of things that hold, and one the check
            // cannot read leaves its own run-time check standing without costing the others theirs.
            // That it stands is carried rather than dropped — the other conjunct being discharged is
            // not the invariant proven.
            return obligations(b.left(), k, at, unnamed, true, decidesFalse, way, per)
                    .and(obligations(b.right(), k, at, unnamed, true, decidesFalse, way, per));
        }
        Core under = Conditions.negated(inv);
        if (under != null) {
            return obligations(under, k, at, unnamed, !positive, decidesFalse, way, per);
        }
        Boolean folded = decidedAt(inv);
        if (folded != null) {
            // The clause folds once the construction's own expressions stand where it read a field.
            // Folding the way it is read owes nothing; folding the other way is a violation, and
            // saying so needs no term to be named. Read under a denial it is the other answer that
            // discharges, which is why the polarity is asked.
            if (folded == positive) {
                return Owed.decided(true);
            }
            if (decidesFalse) {
                return Owed.decided(false).and(Owed.of(VIOLATED));
            }
        }
        // Either it did not fold, or it folded the other way and this caller does not report that as
        // a violation — folding the way it is read returned above. What it owes is read on,
        // unchanged, and the fold is said beside it: a reader classifying the clause needs it, and
        // taking the reading away here would change what this caller is answered.
        Fold fold = folded == null ? Fold.NOT_DECIDED : Fold.FAILS;
        NumericConstraint numeric = null;
        Piecewise piecewise = null;
        if (inv instanceof Core.Binary b && Conditions.relOf(b.op()) != null) {
            Rel eff = positive ? Conditions.relOf(b.op()) : Conditions.negateRel(Conditions.relOf(b.op()));
            LinearForm<FactSubject> la = eff == null ? null : terms.affineOf(b.left(), at);
            LinearForm<FactSubject> ra = eff == null ? null : terms.affineOf(b.right(), at);
            // Asked of the relation, not of its two sides. An atom on both sides cancels, and one
            // that is not in the relation is not something the relation depends on — turning a clause
            // away for a value it does not actually rest on would report nothing about a value the
            // author was never asked about.
            LinearForm<FactSubject> between = la == null || ra == null ? null : la.minus(ra);
            if (between != null && canBeDischargedFrom(between, k, way)) {
                numeric = new NumericConstraint(between, eff);
                // The same clause read as the cases of whatever chooses inside it. Both readings are
                // kept: a guard may name the call itself, which the clause as it stands is what
                // settles, and reading it case by case never takes that away.
                piecewise = piecewiseOf(numeric, inv, at);
            }
        }
        Conditions.Polar polar = Conditions.polar(inv, positive);
        // A predicate over a value no guard could be written about is not a predicate a guard will
        // settle, so it is not owed as one — where the domain can say something of that value it has
        // already said it above, and where it cannot the run-time check stands for the clause.
        List<FactSubject> keys = !unnamed.isEmpty() && names(polar.expr(), unnamed)
                ? List.of() : factKeys(polar.expr(), at);
        boolean stated = polar.positive();
        Fact fact = keys.isEmpty() ? null : new Fact(stated ? keys : firstOnly(keys), stated);
        if (numeric == null && fact == null) {
            return Owed.unreadable(inv).alsoFolded(fold);
        }
        List<NumericConstraint> known = new ArrayList<>();
        sizeFacts(inv, at, known);
        resultFacts(inv, at, known);
        return Owed.of(new Clause(numeric, fact, known, piecewise)).alsoFolded(fold);
    }

    /**
     * Whether there is anything for a clause written over {@code form} to be discharged from.
     *
     * <p>The same question {@link Terms#reportableSite} asks of a value, asked here of the atoms a
     * clause is written over — and it has to be asked here as well, because a clause reaches atoms
     * the site's own value never mentions. An atom is either one the check writes about of its own
     * accord, which is what a place is, or one something on this path has spoken of. There is no
     * third kind, and for an atom the first reduces to a single test: only an atom standing on one
     * evaluation is outside what the seeding writes about.
     *
     * <p>Asked at all only because identity closed. A form being built used to be evidence that
     * something was known, because a value nothing could be said of could not be composed into a form
     * either; now every value has an identity and arithmetic composes over any of them, so the
     * coincidence is gone and the rule it stood for has to be stated. Left unstated, a clause over a
     * value nothing has ever mentioned would be owed here, and owing it would mean reporting a
     * construction no guard an author could write would ever settle.
     */
    private static boolean canBeDischargedFrom(LinearForm<FactSubject> form, Known k, Read way) {
        return way == Read.AN_ASSUMPTION || form.coefs().keySet().stream()
                .allMatch(atom -> !atom.identity().standsOnAnEvaluation() || k.speaksOf(atom));
    }

    /** Whether {@code inv} is decided outright: the clause, with the construction's own values
     * already standing where it read a field, folded. {@code null} where it does not fold — which is
     * every clause reading anything computed at run time. */
    Boolean decidedAt(Core inv) {
        Object folded = Terms.folded(inv);
        return folded instanceof Boolean b ? b : null;
    }

    static List<FactSubject> firstOnly(List<FactSubject> keys) {
        return keys.isEmpty() ? keys : List.of(keys.get(0));
    }

    /**
     * What taking a condition as holding came to.
     *
     * <p>Two things and not one. A condition of a shape no rule here reads leaves what is known
     * exactly as it was, and so does one that was read and ruled nothing out — the states are
     * identical, and only the reading knows which happened. Answered here rather than guessed at
     * afterwards by comparing the state to what went in: that comparison says whether anything
     * changed, which is a third question and is the answer to neither.
     *
     * @param read whether any of these domains took the condition in
     */
    record Assumed(Known known, boolean taken, boolean shapeRead) {

        Assumed alsoRead(boolean moreTaken, boolean moreShape) {
            return moreTaken && !taken || moreShape && !shapeRead
                    ? new Assumed(known, taken || moreTaken, shapeRead || moreShape) : this;
        }
    }

    /** Refines {@code k} by asserting {@code cond} (or its negation): a comparison tightens the
     * numeric domain, a stdlib predicate settles a fact. A condition of neither shape, and an operand
     * outside the affine fragment, leave {@code k} unchanged (sound). */
    Assumed assumeCond(Core rawCond, Known k, Denotations at, boolean positive) {
        Core cond = Conditions.asSizeComparison(rawCond);
        // Two answers, and they were one until a condition could name something without this having
        // read what it says. What was taken in is what a proof about this path may rest on; what was
        // read is what an unsettled arm may be explained by. A condition whose shape ran out still
        // narrows the state through the subject it names, and a proof that left it out would name a
        // set of conditions that can all hold and say they cannot.
        boolean taken = false;
        boolean shapeRead = false;
        Core ordered = Conditions.asOrderComparison(terms, cond, at);
        if (ordered != cond) {
            // Both hold of the same values: the order the call decides, and the bound on the sign
            // that decides it. Which one a clause is read against is settled where the clause is
            // read, so a guard states each of them rather than choosing here.
            Assumed first = assumeCond(ordered, k, at, positive);
            k = first.known();
            taken = first.taken();
            shapeRead = first.shapeRead();
        }
        // `&&` asserted true gives both sides; `||` asserted false gives both sides negated.
        if (cond instanceof Core.Binary b
                && (b.op() == BinOp.AND && positive || b.op() == BinOp.OR && !positive)) {
            Assumed left = assumeCond(b.left(), k, at, positive);
            // Either side taken in is the condition taken in. A conjunction one half of which reads
            // is not one nothing was read of, and calling it that would name this compiler's limit
            // where the limit was reached on one operand only.
            return assumeCond(b.right(), left.known(), at, positive)
                    .alsoRead(left.taken() || taken, left.shapeRead() || shapeRead);
        }
        Core under = Conditions.negated(cond);
        if (under != null) {
            return assumeCond(under, k, at, !positive).alsoRead(taken, shapeRead);
        }
        Known out = k;
        // What holds of the sizes the condition names, and of what the operations in it answer,
        // whichever way the condition itself is read.
        List<NumericConstraint> known = new ArrayList<>();
        sizeFacts(cond, at, known);
        resultFacts(cond, at, known);
        for (NumericConstraint c : known) {
            // A size is never negative whether or not the condition holds, so this holds of the value
            // and not of the path — the condition is only where the container got named.
            out = out.taking(c.form(), c.rel(), Known.Held.OF_THE_VALUE, terms.kindsOf(c.form()));
        }
        // A condition no case of what it is written over can satisfy is one this branch is never
        // entered under, and a value the program never builds is not one to report about. Asked of
        // everything the condition itself established and not only of what held on the way in: a
        // size and what an operation answers hold of the value however the condition comes out, and
        // a case read without them is one this would call reachable where the construction below,
        // which is handed the same facts, would not.
        if (noCaseSatisfies(cond, out, at, positive)) {
            // Read, and read to the end: what it comes to is that nothing enters here.
            return new Assumed(out.reachingNothing(), true, true);
        }
        taken |= !known.isEmpty();
        shapeRead |= !known.isEmpty();
        if (cond instanceof Core.Binary b) {
            Rel rel = Conditions.relOf(b.op());
            Rel eff = rel == null ? null : positive ? rel : Conditions.negateRel(rel);
            LinearForm<FactSubject> la = eff == null ? null : terms.affineOf(b.left(), at);
            LinearForm<FactSubject> ra = eff == null ? null : terms.affineOf(b.right(), at);
            if (la != null && ra != null) {
                LinearForm<FactSubject> compared = la.minus(ra);
                out = out.taking(compared, eff, Known.Held.ON_THE_PATH, terms.kindsOf(compared));
                taken = true;
                shapeRead |= readsItsShape(b.left(), at) && readsItsShape(b.right(), at);
            }
            // What the comparison named, recorded as spoken about: a construction from one of these
            // is one the author has said something about, whichever route ends up carrying it.
            Set<FactSubject> named = new HashSet<>(spokenOf(b.left(), at, la));
            named.addAll(spokenOf(b.right(), at, ra));
            out = out.speaking(named);
        }
        List<Quantified> quantified = new ArrayList<>();
        quantifiedBy(cond, at, positive, quantified);
        out = out.and(quantified);
        taken |= !quantified.isEmpty();
        shapeRead |= !quantified.isEmpty();
        // Both routes, always: which one carries a clause is decided where the clause is read, and a
        // guard does not know which that will be.
        Conditions.Polar polar = Conditions.polar(cond, positive);
        FactSubject key = terms.subjectOf(polar.expr(), at);
        return key == null ? new Assumed(out, taken, shapeRead)
                : new Assumed(out.taking(key, polar.positive(), Known.Held.ON_THE_PATH), true,
                        shapeRead || readsItsShape(polar.expr(), at));
    }

    /**
     * Whether a rule here read the shape {@code e} is written in.
     *
     * <p>Not what a fact about {@code e} is filed under, which is {@link Terms#subjectOf}'s and is
     * now an answer for every expression there is. This is the other question, and the only place
     * the symbolic reading is the right one to ask: whether the check reached what the condition
     * <em>says</em>, or only which value it says it of.
     *
     * <p>What it decides is what an unsettled arm is explained by. A condition of a shape no rule
     * reads is this compiler's limit and widening the reading removes it; a condition read to no
     * effect is the ordinary state of a branch nobody built a value for, and no widening touches it.
     * Since identity closed, every condition names something and a fact about that something is
     * always recorded — so answering this from whether anything was recorded made the first kind
     * vanish, and every limit of this compiler was reported as a fact about the model. Measured:
     * over the whole suite the first kind stopped occurring at all.
     *
     * <p>The knowledge is taken in either way. What a guard says about a value is true whether or not
     * this check could read the shape it was written in, and a clause naming that value is still
     * discharged by it. This says only what may be claimed about the reading.
     */
    private boolean readsItsShape(Core e, Denotations at) {
        return terms.bodyKey(e, at) != null;
    }

    /** The terms one side of a compared pair names: the expression itself, and each atom of the form it
     * reduced to — {@code leftover + 1} says something about {@code leftover}. */
    Collection<FactSubject> spokenOf(Core side, Denotations at, LinearForm<FactSubject> form) {
        Set<FactSubject> named = new HashSet<>(form == null ? Set.of() : form.coefs().keySet());
        FactSubject written = terms.subjectOf(side, at);
        if (written != null) {
            named.add(written);
        }
        return named;
    }



    /**
     * The positions this reading took {@code owed}'s clause in about.
     *
     * <p>What the reading produced and not what it was handed. A comparison it could not put in
     * linear form still comes back as a statement — over an atom standing for the whole expression,
     * which is not the position — so a caller asking whether this reading adopted a clause at a
     * position asks this and gets the reading's own answer. Worked out from the clause's spelling
     * instead, {@code value * 2 >= 4} and {@code value * value >= 4} are one shape, and the first is
     * read whole while the second is read about nothing.
     */
    static Set<FactSubject> subjectsIn(Owed owed) {
        Set<FactSubject> named = new LinkedHashSet<>();
        for (Part eachC : owed.parts()) {
            if (!(eachC instanceof Part.Carried carriedC)) {
                continue;
            }
            Clause c = carriedC.clause();
            for (NumericConstraint known : c.known()) {
                named.addAll(known.form().coefs().keySet());
            }
            if (c.numeric() != null) {
                named.addAll(c.numeric().form().coefs().keySet());
            }
            if (c.fact() != null) {
                named.addAll(c.fact().keys());
            }
        }
        return named;
    }

    /**
     * The atoms a projection could narrow by, of what {@code owed} states.
     *
     * <p>{@link #subjectsIn} counts the key a guard settles by name as well, because what makes a
     * clause readable against a value is that something speaks of it, however it speaks. This
     * counts what the interval algebra was handed a form for, which is the narrower thing and the
     * one a range's exactness is about: {@code value == 3 || value == 5} arrives as a fact keyed on
     * the comparison and no form at all, so it names a subject there and narrows nothing here.
     */
    static Set<FactSubject> narrowableIn(Owed owed) {
        Set<FactSubject> named = new LinkedHashSet<>();
        for (Part eachC : owed.parts()) {
            if (!(eachC instanceof Part.Carried carriedC)) {
                continue;
            }
            Clause c = carriedC.clause();
            // What the clause states, and not what holds of the operations it names.
            // {@link Clause#known} is filled by {@link #sizeFacts} and {@link #resultFacts} with
            // relations that are true of every value — a size is never negative — so counting them
            // would call any rule mentioning a size a rule that narrowed the size, whatever it says
            // about it.
            if (c.numeric() != null) {
                named.addAll(c.numeric().atoms());
            }
        }
        return named;
    }

    /** {@code k} with everything {@code owed} states taken as holding, as far as {@code held}
     * reaches. What a clause owes at a construction is what it guarantees where it is already
     * established, so the two read the same clauses through the same rule and differ only in
     * direction. */
    Known assume(Owed owed, Known k, Known.Held held) {
        Known out = k;
        // Every subject this takes something in about is one something has been said about. Recorded
        // for the same reason a guard's subjects are: what makes a clause readable against a value is
        // that something speaks of it, and the seeding speaks. A place did not need it — the seeding
        // writes about places, which is a rule of its own — but an evaluation has no such rule, and
        // saying nothing here would leave a value its own type guarantees something about looking
        // like one nothing is known of.
        out = out.speaking(subjectsIn(owed));
        // What could not be read says nothing here: a clause left to the run-time check is not one
        // the seeding may assume, and the flag saying so is the construction site's to act on.
        for (Part eachC : owed.parts()) {
            if (!(eachC instanceof Part.Carried carriedC)) {
                continue;
            }
            Clause c = carriedC.clause();
            for (NumericConstraint known : c.known()) {
                // What is known of a size holds of the container itself, whatever established the
                // clause it was read out of.
                out = out.taking(known.form(), known.rel(), Known.Held.OF_THE_VALUE,
                        terms.kindsOf(known.form()));
            }
            if (c.numeric() != null) {
                out = out.taking(c.numeric().form(), c.numeric().rel(), held,
                        terms.kindsOf(c.numeric().form()));
            }
            if (c.fact() != null) {
                // What is guaranteed is guaranteed of the term as written; a container built from it
                // is another term, and reads the rules where it is constructed rather than here.
                out = out.taking(c.fact().keys().get(0), c.fact().positive(), held);
            }
        }
        return out;
    }

    // --- affine forms --------------------------------------------------------------------------

    /** What is known of the size of every container an expression names: never negative, and no
     * greater than the size of what it was built from wherever the building can only drop elements. */
    void sizeFacts(Core e, Denotations at, List<NumericConstraint> out) {
        // A name is what it was given, here as everywhere: what is known of a size does not depend on
        // whether the size was written where it is read or bound first.
        if (e instanceof Core.Read r && at.valueOf(r.binding()) != null) {
            sizeFacts(at.valueOf(r.binding()), at, out);
            return;
        }
        if (!(e instanceof Core.PreservedCall call)) {
            Core.forEachChild(e, child -> sizeFacts(child, at, out));
            return;
        }
        Core container = DischargeRules.sizeArgOf(call);
        if (container != null) {
            // The subject and not the symbolic key: a size is never negative whatever it is taken
            // of, and a count over something the term grammar cannot read is still a count.
            FactSubject atom = terms.subjectOf(call, at);
            if (atom != null) {
                out.add(new NumericConstraint(LinearForm.atom(atom), Rel.GE));   // a size is never negative
                bounds(call.operation(), DischargeRules.sizeSource(container), at, out);
            }
        }
        for (Core arg : call.args()) {
            sizeFacts(arg, at, out);
        }
    }

    /**
     * What is known of the result of every operation an expression names, whatever its arguments are:
     * an absolute value is not negative, a remainder by a written divisor is below it.
     *
     * <p>The sibling of {@link #sizeFacts}, and read in both the places that one is: what an
     * operation guarantees holds where a clause is read against the call and where a condition names
     * it alike. A bound whose rule asks something of the arguments is stated only where the arguments
     * answer, and what they are read as is this reading's answer — a name given a constant is that
     * constant, here as everywhere.
     */
    void resultFacts(Core e, Denotations at, List<NumericConstraint> out) {
        // A name is what it was given, as in `sizeFacts`: an operation's guarantee does not depend on
        // whether its call was written where it is read or bound first.
        if (e instanceof Core.Read r && at.valueOf(r.binding()) != null) {
            resultFacts(at.valueOf(r.binding()), at, out);
            return;
        }
        if (!(e instanceof Core.PreservedCall call)) {
            Core.forEachChild(e, child -> resultFacts(child, at, out));
            return;
        }
        FactSubject result = terms.atomOf(call, at);
        if (result != null) {
            for (DischargeRules.ResultBound bound
                    : DischargeRules.boundsOn(call, arg -> constantOf(arg, at))) {
                LinearForm<FactSubject> against = bound.against() == null
                        ? LinearForm.constant(bound.offset())
                        : addTo(terms.affineOf(bound.against().of(call), at), bound.offset());
                if (against != null) {
                    out.add(new NumericConstraint(LinearForm.atom(result).minus(against), bound.rel()));
                }
            }
        }
        shiftFact(call, at, out);
        for (Core arg : call.args()) {
            resultFacts(arg, at, out);
        }
    }

    /**
     * Whether {@code cond}, asserted with polarity {@code positive}, fails in every case an
     * operation inside it is defined in — so the branch it guards is not entered.
     *
     * <p>The same reading the construction below does, done where the condition is taken instead.
     * Without it what an operation answers is read at one of the two and not the other, and a path
     * the cases show cannot be taken is walked as though it could: the construction under it is then
     * reported against guards that cannot all hold, which is a diagnostic about a value the program
     * never builds.
     */
    private boolean noCaseSatisfies(Core cond, Known k, Denotations at, boolean positive) {
        if (!(cond instanceof Core.Binary b) || Conditions.relOf(b.op()) == null) {
            return false;
        }
        Rel stated = positive ? Conditions.relOf(b.op()) : Conditions.negateRel(Conditions.relOf(b.op()));
        LinearForm<FactSubject> la = stated == null ? null : terms.affineOf(b.left(), at);
        LinearForm<FactSubject> ra = stated == null ? null : terms.affineOf(b.right(), at);
        if (la == null || ra == null) {
            return false;
        }
        Piecewise cases = piecewiseOf(new NumericConstraint(la.minus(ra), stated), cond, at);
        return cases != null && cases.refutedBy(k.numbers());
    }

    /**
     * {@code owed} read as the cases of the one operation inside it that answers a value it was
     * given, or null where there is no such operation, where there is more than one, or where a case
     * could not be read.
     *
     * <p>The substitution is made in the form and not in the expression. What the clause reads may be
     * the call as written or a name that was given it, and both arrive here as the one atom the call
     * keys as — so replacing the atom answers both, where rewriting the expression would answer the
     * first and leave the second saying nothing.
     */
    private Piecewise piecewiseOf(NumericConstraint owed, Core inv, Denotations at) {
        Map<FactSubject, Core.PreservedCall> choosing = new LinkedHashMap<>();
        chosenCalls(inv, at, choosing);
        choosing.keySet().retainAll(owed.form().coefs().keySet());
        if (choosing.size() != 1) {
            return null;
        }
        FactSubject atom = choosing.keySet().iterator().next();
        Core.PreservedCall call = choosing.get(atom);
        BigDecimal coefficient = owed.form().coefs().get(atom);
        List<Case> cases = new ArrayList<>();
        for (DischargeRules.Choice one : DischargeRules.chosenBy(call).cases()) {
            LinearForm<FactSubject> answered = terms.affineOf(one.answers().of(call), at);
            if (answered == null) {
                return null;
            }
            LinearForm<FactSubject> instead = owed.form()
                    .minus(LinearForm.atom(atom).times(coefficient))
                    .plus(answered.times(coefficient));
            List<NumericConstraint> given = new ArrayList<>(one.given().size() + 1);
            Map<FactSubject, Granularity> kinds = new HashMap<>(terms.kindsOf(instead));
            // What the call answers here, said of the call itself: in this case the two are one
            // value. Without it a guard written about the call would stand outside the cases, and a
            // clause could come out established by these and refused by that.
            LinearForm<FactSubject> answeredHere = LinearForm.atom(atom).minus(answered);
            given.add(new NumericConstraint(answeredHere, Rel.EQ));
            kinds.putAll(terms.kindsOf(answeredHere));
            for (DischargeRules.ArgumentsStand stands : one.given()) {
                LinearForm<FactSubject> left = terms.affineOf(stands.left().of(call), at);
                LinearForm<FactSubject> right = terms.affineOf(stands.right().of(call), at);
                if (left == null || right == null) {
                    return null;
                }
                LinearForm<FactSubject> between = left.minus(right);
                given.add(new NumericConstraint(between, stands.rel()));
                kinds.putAll(terms.kindsOf(between));
            }
            cases.add(new Case(new NumericConstraint(instead, owed.rel()), List.copyOf(given),
                    Map.copyOf(kinds)));
        }
        return new Piecewise(List.copyOf(cases));
    }

    /** Every call inside {@code e} that answers one of the values it was given, by the atom it keys
     * as. A name is what it was given, as everywhere else a value is read. */
    private void chosenCalls(Core e, Denotations at, Map<FactSubject, Core.PreservedCall> out) {
        if (e instanceof Core.Read r && at.valueOf(r.binding()) != null) {
            chosenCalls(at.valueOf(r.binding()), at, out);
            return;
        }
        if (e instanceof Core.PreservedCall call && DischargeRules.chosenBy(call) != null) {
            FactSubject atom = terms.atomOf(call, at);
            if (atom != null) {
                out.put(atom, call);
            }
        }
        Core.forEachChild(e, child -> chosenCalls(child, at, out));
    }

    /**
     * What {@code call} states through the measure that counts what it shifted and what it answered
     * apart, where it is a shift this has a rule about.
     *
     * <p>The measure over the two values is the atom a clause written in that measure builds, so the
     * fact and the clause meet at one term. Where either value is named by nothing there is no such
     * atom, and nothing is stated.
     */
    private void shiftFact(Core.PreservedCall call, Denotations at, List<NumericConstraint> out) {
        DischargeRules.Shift shift = DischargeRules.shiftBy(call);
        if (shift == null) {
            return;
        }
        Term from = terms.bodyKey(shift.of().of(call), at);
        Term to = terms.bodyKey(call, at);
        LinearForm<FactSubject> amount = terms.affineOf(shift.amount().of(call), at);
        if (from == null || to == null || amount == null) {
            return;
        }
        out.add(new NumericConstraint(
                LinearForm.atom(terms.measureKeyOf(shift.measure(), from, to))
                        .minus(amount.times(shift.per())),
                Rel.EQ));
    }

    /** {@code form} with {@code offset} added, or null where the form could not be read. */
    private static LinearForm<FactSubject> addTo(LinearForm<FactSubject> form, BigDecimal offset) {
        return form == null ? null : form.plus(LinearForm.constant(offset));
    }

    /** The constant {@code e} reads as, or null where it reads as none. */
    private BigDecimal constantOf(Core e, Denotations at) {
        LinearForm<FactSubject> form = terms.affineOf(e, at);
        return form == null || !form.coefs().isEmpty() ? null : form.constant();
    }

    /** How the size of a container relates to the size of what it was built from, down the chain.
     * Which way it is stated is what the construction's {@link Cardinality} says. */
    void bounds(ValueName sizeCall, Core container, Denotations at, List<NumericConstraint> out) {
        // A construction's result is never smaller than each source named for it. A rule may name
        // more than one, so this is a loop where the building below is a single answer — and it is
        // asked of the expression rather than of a call, since `a ++ b` is one of these and is
        // written as an operator.
        for (Core added : DischargeRules.noSmallerThan(container)) {
            stated(sizeCall, container, DischargeRules.sizeSource(added), Rel.GE, at, out);
        }
        if (!(container instanceof Core.PreservedCall call)) {
            return;
        }
        Source built = DischargeRules.builtFrom(call);
        Rel rel = built == null ? null : relationOf(built.size());
        if (rel == null) {
            return;
        }
        stated(sizeCall, container, DischargeRules.sizeSource(built.container()), rel, at, out);
    }

    /** States how the size of {@code container} relates to the size of {@code source}, and goes on
     * down whatever that one was built from. A container neither of them has a key for is one
     * nothing can be said of, and stops the walk. */
    private void stated(ValueName sizeCall, Core container, Core source, Rel rel, Denotations at,
                        List<NumericConstraint> out) {
        Term here = terms.bodyKey(container, at);
        Term there = terms.bodyKey(source, at);
        if (here == null || there == null) {
            return;
        }
        out.add(new NumericConstraint(
                LinearForm.atom(terms.sizeKeyOf(sizeCall, here))
                        .minus(LinearForm.atom(terms.sizeKeyOf(sizeCall, there))),
                rel));
        bounds(sizeCall, source, at, out);
    }

    /** How {@code size} is stated of the two sizes, or null where there is nothing to state: a
     * construction of the same size answers both with one atom ({@code DischargeRules.sizeSource}),
     * so a constraint between them would say a name is itself. */
    private static Rel relationOf(Cardinality size) {
        return switch (size) {
            case AT_MOST -> Rel.LE;
            case SAME -> null;
        };
    }

    /** The keys a guard could have settled to establish this clause: the predicate as written, and
     * the same predicate of each container the written one was built from by a construction that
     * carries it. Stating {@code List.all(p, xs)} is stating it of every sublist of {@code xs}. */
    List<FactSubject> factKeys(Core inv, Denotations at) {
        FactSubject written = terms.subjectOf(inv, at);
        if (written == null) {
            return List.of();
        }
        List<FactSubject> keys = new ArrayList<>();
        keys.add(written);
        if (!(inv instanceof Core.PreservedCall call)) {
            return keys;
        }
        Carrying carried = DischargeRules.carried(call);
        if (carried == null) {
            return keys;
        }
        // The predicate over each container the one it names was built from. The container is the
        // construction's own expression, so the operations peeled off are the ones the body wrote.
        Core container = carried.container();
        Core.PreservedCall stated = call;
        while (container instanceof Core.PreservedCall inner) {
            Source built = DischargeRules.builtFrom(inner);
            if (built == null) {
                break;
            }
            Core.PreservedCall next = carries(stated, carried, inner, built, at);
            if (next == null) {
                break;
            }
            Core source = built.container();
            FactSubject key = terms.subjectOf(carried.over(next, source), at);
            if (key == null) {
                break;
            }
            keys.add(key);
            stated = next;
            container = source;
        }
        return keys;
    }

    /**
     * The predicate as it applies to what {@code inner} was built from, or {@code null} when it does
     * not apply there. A construction the shape carries leaves the predicate as it was. A mapping
     * carries nothing on its own, but a predicate stated over a projection carries when the closure
     * copied that field across, over the field it came from.
     */
    Core.PreservedCall carries(Core.PreservedCall stated, Carrying carried,
                                       Core.PreservedCall inner, Source built, Denotations at) {
        if (carried.through().contains(built.shape())) {
            return stated;
        }
        Projection projection = DischargeRules.projectionOf(stated, at);
        if (built.shape() != Shape.MAPS || projection == null) {
            return null;
        }
        // Where the mapping's closure is written is already stated once, by the table that says which
        // argument each combinator hands its elements to.
        Handed combo = Combinators.handedTo(inner, at);
        if (combo == null) {
            return null;
        }
        Core traced = projectionThrough(projection.projection(), combo.step(), at);
        return traced == null ? null : projection.over(traced);
    }

    /**
     * The projection over an element that a projection over a mapped list reduces to, or
     * {@code null}.
     *
     * <p>{@code .product} over {@code List.map(r -> Line { product = r.product, ... }, xs)} is
     * {@code .product} over {@code xs}: the closure copied that field across, so two mapped elements
     * differ there exactly when the two they came from did. Bounded deliberately — a field a closure
     * computes from others is not this.
     *
     * <p>What comes back is a projection to be keyed and nothing else. A block keys its parameter by
     * where it is bound, so the chain built here is read at the position the closure's parameter
     * stands in, whatever it is called and whatever it was read from.
     */
    Core projectionThrough(Core.Block proj, Core.Block step, Denotations at) {
        if (proj.params().size() != 1 || step.params().size() != 1) {
            return null;
        }
        Core.Binder element = step.params().get(0);
        List<String> read = new Reads(proj.params().get(0).binding()).chain(proj.body());
        if (read == null) {
            return null;
        }
        Reads reads = new Reads(element.binding());
        Core made = reads.produced(step.body());
        List<String> traced;
        if (read.isEmpty()) {
            traced = reads.chain(made);   // the closure hands the element straight back
        } else {
            if (!(made instanceof Core.Construct nd)) {
                return null;
            }
            List<String> copied = null;
            for (Core.FieldValue given : nd.values()) {
                if (given.field().equals(read.get(0))) {
                    copied = reads.chain(given.value());
                }
            }
            if (copied == null) {
                return null;
            }
            traced = new ArrayList<>(copied);
            traced.addAll(read.subList(1, read.size()));
        }
        if (traced == null) {
            return null;
        }
        Core on = Terms.read(element, Terms.elementType(step.type()), step.pos());
        for (String field : traced) {
            on = new Core.FieldAccess(on, field, terms.fieldType(on.type(), field), step.pos());
        }
        return new Core.Block(List.of(element), on, step.type(), step.pos());
    }

    /**
     * What the names in a closure read off the element it is handed: a field chain, or nothing this
     * trace can follow. A binding introduces what it reads <em>where it is written</em> — an expansion
     * splices {@code let $0_r = r in ...} into a closure — so what a name denotes is settled against
     * the bindings before it and not reread later.
     */
    private static final class Reads {

        private final BindingId element;
        private final Map<BindingId, List<String>> chains = new HashMap<>();

        private Reads(BindingId element) {
            this.element = element;
        }

        /** The expression the body produces, with what the bindings on the way there read taken in. */
        Core produced(Core body) {
            Core cur = body;
            while (cur instanceof Core.LetIn li) {
                chains.put(li.binder().binding(), chain(li.value()));
                cur = li.body();
            }
            return cur;
        }

        /** The chain {@code e} reads off the element, or {@code null} if it reads anything else. */
        List<String> chain(Core e) {
            return switch (e) {
                case Core.LetIn li -> {
                    Reads inner = new Reads(element);
                    inner.chains.putAll(chains);
                    inner.chains.put(li.binder().binding(), chain(li.value()));
                    yield inner.chain(li.body());
                }
                case Core.FieldAccess fa -> {
                    List<String> head = chain(fa.target());
                    if (head == null) {
                        yield null;
                    }
                    List<String> out = new ArrayList<>(head);
                    out.add(fa.field());
                    yield out;
                }
                case Core.Read r when chains.containsKey(r.binding()) -> chains.get(r.binding());
                case Core.Read r -> r.binding().equals(element) ? List.of() : null;
                default -> null;
            };
        }
    }

}
