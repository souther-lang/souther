package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.CoverageOrigin;
import souther.compiler.check.Combinators.Handed;
import souther.compiler.check.DischargeRules.Cardinality;
import souther.compiler.check.DischargeRules.Carrying;
import souther.compiler.check.DischargeRules.Projection;
import souther.compiler.check.DischargeRules.Shape;
import souther.compiler.check.DischargeRules.Source;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collection;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.HashSet;
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
            String key = terms.bodyKey(source, at);
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
                Map.of(q.predicate().params().get(0).id(), element));
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
        Core e = asSizeComparison(raw);
        if (e instanceof Core.Binary b && b.op() == Hir.BinOp.AND && positive) {
            quantifiedBy(b.left(), at, true, out);
            quantifiedBy(b.right(), at, true, out);
            return;
        }
        Core under = negated(e);
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
        String container = terms.bodyKey(carried.container(), at);
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

    record Constraint(LinearForm form, Rel rel) {}

    /**
     * A predicate stated of a term. {@code keys} is the term as written first, then each container it
     * was built from by a construction that carries the predicate — any one of them settled is this
     * clause established. Refuting reads only the first: denying a predicate of a list says nothing
     * about a list built from it. {@code positive} is false for a clause written under a negation,
     * and such a clause carries nowhere, since the implication runs the other way.
     */
    record Fact(List<String> keys, boolean positive) {

        boolean entailedBy(PredicateFacts facts) {
            for (String key : keys) {
                if (facts.entails(key, positive)) {
                    return true;
                }
            }
            return false;
        }

        boolean refutedBy(PredicateFacts facts) {
            return facts.refutes(keys.get(0), positive);
        }
    }

    /** A clause that cannot hold, said in the language the domain reads: {@code -1 >= 0}. */
    static final Clause VIOLATED = new Clause(
            new Constraint(LinearForm.constant(BigDecimal.ONE.negate()), Rel.GE), null, List.of());

    /**
     * One clause of an invariant, and the two ways it can come out: a relation for the domain to
     * prove, and the key a guard restating it settles. Either may be absent, and where both are
     * present either one discharging the clause is enough — a guard is written one way and a clause
     * another, and which of the two routes carries it is not the author's concern.
     */
    record Clause(Constraint numeric, Fact fact, List<Constraint> known) {

        boolean dischargedBy(NumericDomain d, PredicateFacts facts) {
            return numeric != null && d.entails(numeric.form(), numeric.rel())
                    || fact != null && fact.entailedBy(facts);
        }

        boolean refutedBy(NumericDomain d, PredicateFacts facts) {
            return numeric != null && d.refutes(numeric.form(), numeric.rel())
                    || fact != null && fact.refutedBy(facts);
        }
    }

    /**
     * What a clause owes, and whether any part of it was outside what the check can read.
     *
     * <p>The two are apart because a clause owing nothing has two reasons: it folded to what it is
     * read with, or nothing in it could be asked here. A conjunction can be both at once — one
     * conjunct discharged and the next unreadable — and reporting only the obligations would say the
     * invariant was proven when half of it was never read.
     *
     * @param clauses what is owed, which the reading discharges or refutes
     * @param unreadable whether a conjunct of it names something the check cannot read here, whose
     *                   run-time check stands whatever the rest comes out as
     */
    record Owed(List<Clause> clauses, boolean unreadable) {

        static final Owed NOTHING = new Owed(List.of(), false);
        static final Owed UNREADABLE = new Owed(List.of(), true);

        static Owed of(Clause clause) {
            return new Owed(List.of(clause), false);
        }

        /** Both conjuncts of one clause: everything either owes, unreadable if either was. */
        Owed and(Owed other) {
            List<Clause> both = new ArrayList<>(clauses);
            both.addAll(other.clauses);
            return new Owed(List.copyOf(both), unreadable || other.unreadable);
        }
    }

    /** What {@code inv} owes, where {@code decidesFalse} says a clause folding to the other answer
     * than it is read with is this check's to report. A newtype's constant construction is checked
     * elsewhere, and that check names the clause that failed rather than only saying one did, so it
     * is left to say it. */
    Owed obligations(Core inv, Known k, Denotations at, boolean decidesFalse) {
        return obligations(inv, k, at, Set.of(), true, decidesFalse);
    }

    /** The same, where {@code unnamed} holds the values the site hands over that no clause may be
     * read against. */
    Owed obligations(Core inv, Known k, Denotations at, Set<Core> unnamed,
                     boolean decidesFalse) {
        return obligations(inv, k, at, unnamed, true, decidesFalse);
    }

    /**
     * A clause is read as the comparison it states, and where an order call states one there are two
     * readings of it: the order the call decides, and the bound on the sign that decides it. Which of
     * them this construction can be read against is not known until it is read — a date the check can
     * name is one thing, and the date a day after it is another — so the one that answers is the one
     * taken. Reading a predicate never takes a reading away.
     */
    private Owed obligations(Core rawInv, Known k, Denotations at, Set<Core> unnamed,
                             boolean positive, boolean decidesFalse) {
        Core sized = asSizeComparison(rawInv);
        Core ordered = asOrderComparison(sized, at);
        Owed read = read(ordered, k, at, unnamed, positive, decidesFalse);
        return ordered != sized && read.unreadable()
                ? read(sized, k, at, unnamed, positive, decidesFalse) : read;
    }

    /** What {@code inv} owes, read as it stands. Its parts are read through {@link #obligations},
     * which is where each of them is taken as the comparison it states. */
    private Owed read(Core inv, Known k, Denotations at, Set<Core> unnamed,
                      boolean positive, boolean decidesFalse) {
        if (inv instanceof Core.Binary b && b.op() == Hir.BinOp.AND && positive) {
            // Each conjunct on its own: an invariant is a set of things that hold, and one the check
            // cannot read leaves its own run-time check standing without costing the others theirs.
            // That it stands is carried rather than dropped — the other conjunct being discharged is
            // not the invariant proven.
            return obligations(b.left(), k, at, unnamed, true, decidesFalse)
                    .and(obligations(b.right(), k, at, unnamed, true, decidesFalse));
        }
        Core under = negated(inv);
        if (under != null) {
            return obligations(under, k, at, unnamed, !positive, decidesFalse);
        }
        Boolean folded = decidedAt(inv);
        if (folded != null) {
            // The clause folds once the construction's own expressions stand where it read a field.
            // Folding the way it is read owes nothing; folding the other way is a violation, and
            // saying so needs no term to be named. Read under a denial it is the other answer that
            // discharges, which is why the polarity is asked.
            if (folded == positive) {
                return Owed.NOTHING;
            }
            if (decidesFalse) {
                return Owed.of(VIOLATED);
            }
        }
        Constraint numeric = null;
        if (inv instanceof Core.Binary b && relOf(b.op()) != null) {
            Rel eff = positive ? relOf(b.op()) : negateRel(relOf(b.op()));
            LinearForm la = eff == null ? null : terms.affineOf(b.left(), at, k);
            LinearForm ra = eff == null ? null : terms.affineOf(b.right(), at, k);
            if (la != null && ra != null) {
                numeric = new Constraint(la.minus(ra), eff);
            }
        }
        Polar polar = polar(inv, positive);
        // A predicate over a value no guard could be written about is not a predicate a guard will
        // settle, so it is not owed as one — where the domain can say something of that value it has
        // already said it above, and where it cannot the run-time check stands for the clause.
        List<String> keys = !unnamed.isEmpty() && names(polar.expr(), unnamed)
                ? List.of() : factKeys(polar.expr(), at);
        boolean stated = polar.positive();
        Fact fact = keys.isEmpty() ? null : new Fact(stated ? keys : firstOnly(keys), stated);
        if (numeric == null && fact == null) {
            return Owed.UNREADABLE;
        }
        List<Constraint> known = new ArrayList<>();
        sizeFacts(inv, at, known);
        return Owed.of(new Clause(numeric, fact, known));
    }

    /** Whether {@code inv} is decided outright: the clause, with the construction's own values
     * already standing where it read a field, folded. {@code null} where it does not fold — which is
     * every clause reading anything computed at run time. */
    Boolean decidedAt(Core inv) {
        Object folded = Terms.folded(inv);
        return folded instanceof Boolean b ? b : null;
    }

    static List<String> firstOnly(List<String> keys) {
        return keys.isEmpty() ? keys : List.of(keys.get(0));
    }

    /** Refines {@code k} by asserting {@code cond} (or its negation): a comparison tightens the
     * numeric domain, a stdlib predicate settles a fact. A condition of neither shape, and an operand
     * outside the affine fragment, leave {@code k} unchanged (sound). */
    Known assumeCond(Core rawCond, Known k, Denotations at, boolean positive) {
        Core cond = asSizeComparison(rawCond);
        Core ordered = asOrderComparison(cond, at);
        if (ordered != cond) {
            // Both hold of the same values: the order the call decides, and the bound on the sign
            // that decides it. Which one a clause is read against is settled where the clause is
            // read, so a guard states each of them rather than choosing here.
            k = assumeCond(ordered, k, at, positive);
        }
        // `&&` asserted true gives both sides; `||` asserted false gives both sides negated.
        if (cond instanceof Core.Binary b
                && (b.op() == Hir.BinOp.AND && positive || b.op() == Hir.BinOp.OR && !positive)) {
            return assumeCond(b.right(), assumeCond(b.left(), k, at, positive), at, positive);
        }
        Core under = negated(cond);
        if (under != null) {
            return assumeCond(under, k, at, !positive);
        }
        Known out = k;
        // What holds of the sizes the condition names, whichever way the condition itself is read.
        List<Constraint> known = new ArrayList<>();
        sizeFacts(cond, at, known);
        for (Constraint c : known) {
            // A size is never negative whether or not the condition holds, so this holds of the value
            // and not of the path — the condition is only where the container got named.
            out = out.taking(c.form(), c.rel(), Known.Held.OF_THE_VALUE, terms.kindsOf(c.form()));
        }
        if (cond instanceof Core.Binary b) {
            Rel rel = relOf(b.op());
            Rel eff = rel == null ? null : positive ? rel : negateRel(rel);
            LinearForm la = eff == null ? null : terms.affineOf(b.left(), at, out);
            LinearForm ra = eff == null ? null : terms.affineOf(b.right(), at, out);
            if (la != null && ra != null) {
                LinearForm compared = la.minus(ra);
                out = out.taking(compared, eff, Known.Held.ON_THE_PATH, terms.kindsOf(compared));
            }
            // What the comparison named, recorded as spoken about: a construction from one of these
            // is one the author has said something about, whichever route ends up carrying it.
            Set<String> named = new HashSet<>(spokenOf(b.left(), at, la));
            named.addAll(spokenOf(b.right(), at, ra));
            out = out.speaking(named);
        }
        List<Quantified> quantified = new ArrayList<>();
        quantifiedBy(cond, at, positive, quantified);
        out = out.and(quantified);
        // Both routes, always: which one carries a clause is decided where the clause is read, and a
        // guard does not know which that will be.
        Polar polar = polar(cond, positive);
        String key = terms.bodyKey(polar.expr(), at);
        return key == null ? out : out.taking(key, polar.positive(), Known.Held.ON_THE_PATH);
    }

    /** The terms one side of a compared pair names: the expression itself, and each atom of the form it
     * reduced to — {@code leftover + 1} says something about {@code leftover}. */
    Collection<String> spokenOf(Core side, Denotations at, LinearForm form) {
        Set<String> named = new HashSet<>(form == null ? Set.of() : form.coefs().keySet());
        String written = terms.bodyKey(side, at);
        if (written != null) {
            named.add(written);
        }
        return named;
    }

    /** A predicate as one of {@code ==}/{@code <} states it, and whether it is being stated or denied. */
    record Polar(Core expr, boolean positive) {}

    /**
     * {@code e}, asserted with polarity {@code positive}, as the comparison of {@code ==} or {@code <}
     * that says the same thing: {@code a /= b} is {@code a == b} denied, {@code a >= b} is
     * {@code a < b} denied, and {@code a > b} is {@code b < a}. A fact is settled by key equality, so
     * without this the six ways to compare two terms are six facts, and a guard written one way would
     * leave a clause written the other unsettled.
     */
    static Polar polar(Core e, boolean positive) {
        if (!(e instanceof Core.Binary b) || relOf(b.op()) == null) {
            return new Polar(e, positive);
        }
        return switch (b.op()) {
            case NE -> new Polar(comparison(Hir.BinOp.EQ, b.left(), b.right(), b), !positive);
            case GE -> new Polar(comparison(Hir.BinOp.LT, b.left(), b.right(), b), !positive);
            case GT -> new Polar(comparison(Hir.BinOp.LT, b.right(), b.left(), b), positive);
            case LE -> new Polar(comparison(Hir.BinOp.LT, b.right(), b.left(), b), !positive);
            default -> new Polar(e, positive);
        };
    }

    static Core.Binary comparison(Hir.BinOp op, Core left, Core right, Core.Binary of) {
        return new Core.Binary(op, left, right, of.origin(), of.type(), of.pos());
    }

    /** What a negation is applied to, or {@code null} if {@code e} is not one. {@code Bool.not} is an
     * ordinary helper: the analysis representation keeps it as a call, and a clause read off an
     * imported declaration is the body it expands to — {@code if b then false else true} over a
     * binding holding the argument. Both are read. */
    static Core negated(Core e) {
        if (e instanceof Core.PreservedCall call && call.operation().equals(DischargeRules.NOT)
                && call.args().size() == 1) {
            return call.args().get(0);
        }
        if (e instanceof Core.LetIn li) {
            Core inner = negated(li.body());
            return inner instanceof Core.Read r && r.binding().equals(li.binder().id())
                    ? li.value() : null;
        }
        return e instanceof Core.If iff
                && iff.then() instanceof Core.Bool t && !t.value()
                && iff.els() instanceof Core.Bool f && f.value()
                ? iff.cond() : null;
    }


    /** {@code k} with everything {@code owed} states taken as holding, as far as {@code held}
     * reaches. What a clause owes at a construction is what it guarantees where it is already
     * established, so the two read the same clauses through the same rule and differ only in
     * direction. */
    Known assume(Owed owed, Known k, Known.Held held) {
        Known out = k;
        // What could not be read says nothing here: a clause left to the run-time check is not one
        // the seeding may assume, and the flag saying so is the construction site's to act on.
        for (Clause c : owed.clauses()) {
            for (Constraint known : c.known()) {
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
    void sizeFacts(Core e, Denotations at, List<Constraint> out) {
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
            String atom = terms.sizeAtomOf(call, arg -> terms.bodyKey(arg, at));
            if (atom != null) {
                out.add(new Constraint(LinearForm.atom(atom), Rel.GE));   // a size is never negative
                bounds(call.operation(), DischargeRules.sizeSource(container), at, out);
            }
        }
        for (Core arg : call.args()) {
            sizeFacts(arg, at, out);
        }
    }

    /** How the size of a container relates to the size of what it was built from, down the chain.
     * Which way it is stated is what the construction's {@link Cardinality} says. */
    void bounds(ValueName sizeCall, Core container, Denotations at, List<Constraint> out) {
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
                        List<Constraint> out) {
        String here = terms.bodyKey(container, at);
        String there = terms.bodyKey(source, at);
        if (here == null || there == null) {
            return;
        }
        out.add(new Constraint(
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
    List<String> factKeys(Core inv, Denotations at) {
        String written = terms.bodyKey(inv, at);
        if (written == null) {
            return List.of();
        }
        List<String> keys = new ArrayList<>();
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
            String key = terms.bodyKey(carried.over(next, source), at);
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
        Hir.Binder element = step.params().get(0);
        List<String> read = new Reads(proj.params().get(0).id()).chain(proj.body());
        if (read == null) {
            return null;
        }
        Reads reads = new Reads(element.id());
        Core made = reads.produced(step.body());
        List<String> traced;
        if (read.isEmpty()) {
            traced = reads.chain(made);   // the closure hands the element straight back
        } else {
            if (!(made instanceof Core.NewData nd) || !nd.spreads().isEmpty()) {
                return null;
            }
            List<String> copied = null;
            for (Core.FieldInit fi : nd.inits()) {
                if (fi.name().equals(read.get(0))) {
                    copied = reads.chain(fi.value());
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
                chains.put(li.binder().id(), chain(li.value()));
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
                    inner.chains.put(li.binder().id(), chain(li.value()));
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

    /**
     * A comparison against zero of an operation answering an order, as the comparison of the two
     * values it orders — or {@code e} unchanged.
     *
     * <p>What such an operation answers is a sign ({@link DischargeRules#orderStatedBy}), so where
     * its answer stands against zero the comparison is between the two arguments themselves. One
     * account: the relation is the one written, taken between the argument a positive answer says is
     * the greater and the other one, so the six relations and the two sides of the zero are all read
     * from the row the library's operation has rather than from a case for each.
     *
     * <p>Only against zero. A sign compared with anything else bounds how far the answer is from
     * zero, which is a statement about the number and not about the order it decides.
     *
     * <p>And only where both values are ones this check can name. The sign is a number the domain
     * carries whatever it is the order of, so a comparison of two values it cannot name is less than
     * what it already had: a clause reading {@code daysBetween(acquiredOn, lostOn) >= 0} is a bound
     * on that count, and rewriting it into a comparison of two dates the check cannot relate would
     * leave the clause unreadable — a construction dropped from the check where it had been reported.
     * Reading a predicate never takes a reading away.
     */
    Core asOrderComparison(Core e, Denotations at) {
        if (!(e instanceof Core.Binary b) || relOf(b.op()) == null) {
            return e;
        }
        boolean callFirst = b.left() instanceof Core.PreservedCall;
        Core side = callFirst ? b.left() : b.right();
        Core zero = callFirst ? b.right() : b.left();
        if (!(side instanceof Core.PreservedCall call) || call.args().size() != 2
                || !isZero(zero)) {
            return e;
        }
        DischargeRules.PositiveOrder positive = DischargeRules.orderStatedBy(call.operation());
        if (positive == null
                || terms.bodyKey(call.args().get(0), at) == null
                || terms.bodyKey(call.args().get(1), at) == null) {
            return e;
        }
        // The relation the source wrote, read from the sign's side of the zero, and between the
        // arguments in the order this operation counts them.
        Hir.BinOp written = callFirst ? b.op() : mirrored(b.op());
        return comparison(written, positive.greaterOf(call), positive.lesserOf(call), b);
    }

    /** Whether {@code e} is the number zero as written. */
    private static boolean isZero(Core e) {
        return e instanceof Core.Int i && i.value() == 0
                || e instanceof Core.Decimal d && d.value().signum() == 0;
    }

    /** {@code op} with its two sides exchanged: what the same fact is called when it is written the
     * other way round. */
    static Hir.BinOp mirrored(Hir.BinOp op) {
        return switch (op) {
            case LT -> Hir.BinOp.GT;
            case GT -> Hir.BinOp.LT;
            case LE -> Hir.BinOp.GE;
            case GE -> Hir.BinOp.LE;
            default -> op;
        };
    }

    /** An emptiness check as the comparison it means, or {@code e} unchanged. */
    static Core asSizeComparison(Core e) {
        if (e instanceof Core.PreservedCall call && call.args().size() == 1
                && DischargeRules.sizeMeantBy(call.operation()) != null) {
            Core size = new Core.PreservedCall(DischargeRules.sizeMeantBy(call.operation()), call.args(),
                    Type.INT, call.pos());
            return new Core.Binary(Hir.BinOp.EQ, size, new Core.Int(0, Type.INT, call.pos()),
                    CoverageOrigin.unwritten(),
                    Type.BOOL, call.pos());
        }
        return e;
    }


    static Rel relOf(Hir.BinOp op) {
        return switch (op) {
            case GE -> Rel.GE;
            case GT -> Rel.GT;
            case LE -> Rel.LE;
            case LT -> Rel.LT;
            case EQ -> Rel.EQ;
            case NE -> Rel.NE;
            default -> null;
        };
    }

    static Rel negateRel(Rel rel) {
        return switch (rel) {
            case GE -> Rel.LT;
            case GT -> Rel.LE;
            case LE -> Rel.GT;
            case LT -> Rel.GE;
            case EQ -> Rel.NE;
            case NE -> Rel.EQ;
        };
    }
}
