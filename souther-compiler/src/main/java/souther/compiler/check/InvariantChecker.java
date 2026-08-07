package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.check.Combinators.Handed;
import souther.compiler.check.NumericDomain.LinearForm;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The intraprocedural invariant-discharge check (spec §invariant-discharge). It walks a behavior's
 * body threading what holds where it stands ({@link Known}), seeded from the input types'
 * invariants and refined along each {@code guard}/{@code if} guard (a {@code guard} is already an
 * {@code if} here). At every construction whose invariant it can carry, it asks whether what is known
 * there <em>discharges</em> it, or refutes it. A construction proven to violate its invariant on a
 * reachable path is a compile error (the path-sensitive generalization of the constant check
 * {@code Amount(-5)}); one it cannot prove is a warning (a possible abort — guard it, or reify the
 * relation into a type invariant). An invariant naming something it cannot name is left opaque (no
 * diagnostic; the run-time check stays), so every flagged construction is one whose clauses could be
 * read at the values it is being given.
 *
 * <p>A violation is reported in the terms it was reached in, and no stronger: {@link Known} carries
 * beside itself the reading with nothing a condition on the path settled, and a clause that reading
 * already refutes is one the construction fails wherever it is written. Which of the things known
 * here settled the rest is not asked — nothing records what a refutation used, so a violation the
 * values alone do not settle is said that way and not blamed on a guard.
 *
 * <p>What it reads is Core: the body in the representation the rules are written at
 * ({@link InliningPolicy#DISCHARGE}), typed by the checker like any other, and each declaration's
 * invariant typed the same way against the fields it is written over. A clause is then read at a
 * construction by putting the value each field is being given where that field is read — one
 * expression in one representation, so what a clause says and what the body says meet as terms
 * rather than as two spellings that have to be kept agreeing.
 *
 * <p>Which value a fact is about is the binding a name was answered with ({@link Location}), so a
 * body that binds one spelling twice states two things and nothing has to be forgotten when it does.
 *
 * <p>What is here is the walk: where to look, what is known where, and what to say about a
 * construction. What it looks <em>with</em> is beside it — {@link DischargeRules} for what the
 * language's operations keep, {@link Clauses} for a declaration's invariant read at a value,
 * {@link Terms} for where a value is and what can be said of it, {@link Predicates} for what a clause
 * owes and what a guard settles. Each of those is a question with one answer, and the walk is what
 * asks them in order.
 *
 * <p>The walk mirrors {@link TotalityChecker}: a {@code switch} over {@link Core} threading an
 * immutable environment. It is fail-open — any internal error is swallowed so an analysis bug can
 * never reject a valid program.
 */
public final class InvariantChecker {

    record Findings(List<CompileException> errors, List<Diagnostic> warnings) {}

    /**
     * What this check reads: one behavior's body and the invariants of the types around it, both in
     * the representation the rules are written at ({@link InliningPolicy#DISCHARGE}) rather than the
     * one the backend emits from.
     *
     * <p>{@code invariants} holds the declarations of the module being checked. A type another module
     * declares is absent, and its clause is read off the declaration in the settled form — where the
     * operations have already become the folds they are, so it falls outside the fragment.
     */
    public record Source(Ast.Expr body, Map<TypeName, List<Ast.InvariantClause>> invariants) {}

    /** How many conditionals a construction opens before the rest is left to the run-time check.
     * Each one doubles the paths, and a value written over three of them is not what the bound is
     * protecting against so much as what it declines to spend the time on. */
    private static final int BRANCHES_OPENED = 3;

    /** How far into a value's fields the seeding reads. A type's own invariant is what its fields
     * guarantee, and a field's type carries its own; past a couple of levels what a clause could be
     * read against is a value the body would have had to name, and it names it by reading it. */
    private static final int FIELDS_SEEDED = 2;

    private final Symbols symbols;
    /** The declarations' invariants, typed where they are declared and read where a value is built. */
    private final Clauses clauses;
    /** Where a value is, what it is called, and what can be said of it. */
    private final Terms terms;
    /** What a clause owes and what a guard settles. */
    private final Predicates predicates;
    private final List<CompileException> errors = new ArrayList<>();
    private final List<Diagnostic> warnings = new ArrayList<>();

    private InvariantChecker(Symbols symbols,
                             Map<TypeName, List<Ast.InvariantClause>> dischargeInvariants) {
        this.symbols = symbols;
        this.clauses = new Clauses(symbols, dischargeInvariants);
        this.terms = new Terms(symbols);
        this.predicates = new Predicates(terms);
    }

    /**
     * How a clause of {@code data}'s invariant can be discharged, read on its own — the construction
     * is assumed to name what it is given, so what is left is the clause's own shape. {@code at} is
     * where the clause is written, which is the pre-expansion position; {@code clause} is that clause
     * in the representation the check reads.
     */
    public static ClauseDischarge capabilityOf(Ast.Expr clause, SourcePos at, Ast.Data data,
                                               Symbols symbols) {
        InvariantChecker c = new InvariantChecker(symbols, Map.of());
        // Read over the declaration's own fields, each standing for itself: a construction hands one
        // value per field, so a clause naming a field names something wherever it is built. These
        // stand for a value rather than holding one, so they are entered as locations and nothing is
        // seeded of them — what a clause owes is the question, and answering it here would be
        // assuming it.
        Core stated = c.clauses.typed(clause, data);
        Denotations fields = Denotations.none().locations(c.clauses.bindingsOf(data).values());
        List<Predicates.Clause> owed;
        try {
            owed = stated == null ? null
                    : c.predicates.obligations(stated, Known.top(), fields, false);
        } catch (RuntimeException _) {
            owed = null;   // fail-open, as the walk is
        }
        if (owed == null || owed.isEmpty()) {
            return ClauseDischarge.runtimeOnly(at, c.whyUnreadable(stated, fields));
        }
        for (Predicates.Clause owe : owed) {
            if (owe.numeric() != null) {
                return ClauseDischarge.derivable(at);
            }
        }
        return ClauseDischarge.exactMatch(at);
    }

    /** What in {@code clause} the check cannot read, said so an author can act on it. */
    private String whyUnreadable(Core clause, Denotations fields) {
        if (clause == null) {
            return "it is not a rule this check could read as one expression";
        }
        Core blocked = unreadable(clause, fields);
        if (blocked instanceof Core.PreservedCall call) {
            return "it calls `" + call.operation().name()
                    + "`, which the check reads as a value and not as a term";
        }
        if (blocked != null) {
            return "it is not one of the shapes the check reads";
        }
        return "it names a term the check cannot name";
    }

    /** The innermost part of {@code e} the term grammar cannot read, or {@code null} if it reads all
     * of it. Read under the same fields the clause was, so a field it names is a location and what
     * is left is the shape. */
    private Core unreadable(Core e, Denotations fields) {
        Core[] found = {null};
        Core.forEachChild(e, child -> {
            if (found[0] == null) {
                found[0] = unreadable(child, fields);
            }
        });
        if (found[0] != null) {
            return found[0];
        }
        return terms.bodyKey(e, fields) == null ? e : null;
    }

    /**
     * Analyzes one behavior body against the bindings its inputs are. Never throws. A {@code null}
     * body is one the analysis representation could not be built or typed for, and is not analyzed at
     * all.
     */
    static Findings analyze(Core body, Map<TypeName, List<Ast.InvariantClause>> invariants,
                            Scope params, Symbols symbols) {
        InvariantChecker c = new InvariantChecker(symbols, invariants);
        if (body == null) {
            return new Findings(c.errors, c.warnings);
        }
        try {
            Entered in = new Entered(Known.top(), Denotations.none());
            for (Map.Entry<BindingId, Scope.Binding> p : params.bindings().entrySet()) {
                in = c.enter(new Core.Read(p.getValue().name(), p.getKey(), p.getValue().type(),
                        body.pos()), in.known(), in.at());
            }
            c.walk(body, in.known(), in.at(), 0);
        } catch (RuntimeException _) {
            // fail-open: the run-time invariant check remains the backstop
        }
        return new Findings(c.errors, c.warnings);
    }

    // --- the walk ------------------------------------------------------------------------------

    private void walk(Core e, Known k, Denotations at, int depth) {
        Core.If value = conditionalValueIn(e);
        if (value != null && depth < BRANCHES_OPENED) {
            // A conditional in a value position is one of its two branches, and which one is decided
            // by its condition. So this is read once with each standing there, under that condition,
            // and what the two readings find is said once. Every place a conditional can be given —
            // to a field, to a name, to a guard — is this one place.
            walk(value.cond(), k, at, depth);
            Set<Core> alike = sameConditional(e, value, at);
            say(reading(without(e, alike, value.then()),
                            predicates.assumeCond(value.cond(), k, at, true), at, depth),
                    reading(without(e, alike, value.els()),
                            predicates.assumeCond(value.cond(), k, at, false), at, depth));
            return;
        }
        checkIfConstruction(e, k, at, false);
        switch (e) {
            case Core.If iff -> {
                walk(iff.cond(), k, at, depth);
                walk(iff.then(), predicates.assumeCond(iff.cond(), k, at, true), at, depth);
                walk(iff.els(), predicates.assumeCond(iff.cond(), k, at, false), at, depth);
            }
            case Core.IfConstructed ic -> {
                // The attempt's own construction cannot abort — a failing invariant is the else
                // branch — so it is checked for a decided violation and never warned about as a
                // possible one. Its field values are walked on their own so a construction nested
                // inside an argument is still an ordinary, aborting one.
                checkIfConstruction(ic.construct(), k, at, true);
                Core.forEachChild(ic.construct(), child -> walk(child, k, at, depth));
                // Reaching `then` is the construction having held, so the binding carries the type's
                // invariant exactly as an input of that type does — which is a location, and not the
                // construction read again. What the construction denotes is what the check could say
                // of the attempt, and an attempt is written where it could not say enough: an
                // expression it cannot name denotes nothing, and inheriting that would drop the one
                // thing reaching this branch established.
                Entered in = enter(Terms.read(ic.binder(), ic.construct().type(), ic.pos()), k, at);
                walk(ic.then(), in.known(), in.at(), depth);
                // Each departure stands where the invariant did not hold, and nothing was built
                // there, so none of them is seeded with anything the attempt would have guaranteed.
                ic.els().forEach(arm -> walk(arm.body(), k, at, depth));
            }
            case Core.LetIn li -> {
                // A closure is read where it is applied: what its parameter holds is decided there,
                // and reading it here would read every construction in it with the element unknown.
                if (!(li.value() instanceof Core.Block)) {
                    walk(li.value(), k, at, depth);
                }
                // The name is an alias for what its initializer denotes, so what is recorded about it
                // is recorded under that denotation and not under the binding. Recording it under the
                // binding is what made a named subexpression a term of its own, answering differently
                // from the very expression it was given.
                Denotes what = terms.denotationOf(li.value(), at, k);
                Known k2 = k;
                // A binding that denotes what it was given is an alias and introduces no value, so
                // there is nothing to record of it: what holds of what it names already holds.
                // Recording it anyway assigns that name its own form, and an assignment drops what
                // was known of what it assigns to — the bound on it would be lost to the copy. A
                // location is always this; a term is where the form is that term's own atom.
                if (what instanceof Denotes.Term term && terms.isNumeric(li.value().type())) {
                    LinearForm vf = terms.affineOf(li.value(), at, k);
                    if (vf != null && !vf.equals(LinearForm.atom(term.key()))) {
                        k2 = k2.assigning(term.key(), vf);
                    }
                }
                walk(li.body(), k2, at.binding(li.binder().id(), li.value(), what), depth);
            }
            case Core.Match m -> {
                walk(m.scrutinee(), k, at, depth);
                for (Core.Case c : m.cases()) {
                    // A sum has no fields of its own, so the scrutinee is not a location any clause
                    // could have named — the case's value names only itself. What the arm binds is a
                    // value of the case's type, reached only here, so it is a location this arm
                    // introduces and it carries what that type guarantees.
                    if (c.binding() == null || c.bindType() == null) {
                        walk(c.body(), k, at, depth);
                        continue;
                    }
                    Entered in = enter(Terms.read(c.binding(), c.bindType(), c.pos()), k, at);
                    walk(c.body(), in.known(), in.at(), depth);
                }
            }
            case Core.PreservedCall call -> walkCall(call, k, at, depth);
            default -> Core.forEachChild(e, child -> walk(child, k, at, depth));
        }
    }

    /** Walks a call the representation kept standing, entering a combinator closure's parameters as
     * the locations the application introduces — the element at the container's element type, and
     * every other at what the closure was typed with — so a construction inside the closure is
     * analyzed rather than left opaque. A closure is where its parameters are values, which is here
     * and not where the block is written. */
    private void walkCall(Core.PreservedCall call, Known k, Denotations at, int depth) {
        Handed handed = Combinators.handedTo(call, at);
        for (Core arg : call.args()) {
            // The closure is asked by identity: a call may write one expression twice, and only the
            // argument the operation applies is the one an element arrives in.
            if (handed == null || arg != handed.closure()) {
                walk(arg, k, at, depth);
                continue;
            }
            Core container = handed.container();
            Type elem = Terms.elementType(container.type());
            // The container is read where the call is written, so what is known of its elements
            // is looked up before the closure's parameter stands for anything.
            List<Quantified> relations = predicates.elementRelations(container, k, at);
            Core.Read element = Terms.read(handed.element(), elem, handed.step().pos());
            // an element of a container is not a location the body can otherwise name
            Entered in = enter(element, k, at);   // the element carries its type's invariant
            // What a fold hands its step beside the element is a value of the type it was seeded
            // with, built through that type's checked constructor like any other — so it carries
            // that type's invariant, and the accumulator is not the one binding that has to give
            // its newtype up to be reasoned about.
            in = enterOthers(handed, in);
            Known k2 = in.known();
            for (Quantified q : relations) {
                k2 = predicates.instantiate(q, element, k2, in.at());
            }
            walk(handed.step().body(), k2, in.at(), depth);
        }
    }

    /** {@code in} with the closure's parameters other than the element entered at the types the
     * closure was typed with. A closure typed as anything but a function hands its parameters
     * nothing this can name, and they stay out. */
    private Entered enterOthers(Handed handed, Entered in) {
        if (!(handed.step().type() instanceof Type.FnOf fn)) {
            return in;
        }
        List<Ast.Binder> params = handed.step().params();
        Entered out = in;
        for (int i = 0; i < params.size() && i < fn.params().size(); i++) {
            if (params.get(i) == handed.element()) {
                continue;
            }
            // A call the representation kept standing was applied to a signature that accepted it,
            // so its closure is typed. Answering an untyped parameter with the element's type would
            // seed another type's invariant at a place this cannot read, so it is not answered.
            Type given = fn.params().get(i);
            if (given == null) {
                throw new IllegalStateException("a closure a preserved call applies has an untyped"
                        + " parameter, so what it is handed cannot be said");
            }
            out = enter(Terms.read(params.get(i), given, handed.step().pos()), out.known(), out.at());
        }
        return out;
    }

    // --- construction detection & discharge check ----------------------------------------------

    private void checkIfConstruction(Core e, Known k, Denotations at, boolean attempted) {
        if (e instanceof Core.NewData nd && nd.spreads().isEmpty()) {
            if (symbols.get(nd.typeName()) instanceof Ast.Data type) {
                report(nd, type, nd.pos(), attempted, verdictOf(nd, type, k, at));
            }
            return;
        }
        // Closed arithmetic over a newtype builds one where it stands: the operands are unwrapped,
        // the operator applied, and the result constructed again, so the invariant is owed here.
        if (Terms.asOperator(e) instanceof Core.Binary bin && Terms.isArith(bin.op())
                && bin.type() instanceof Type.Ref r
                && symbols.get(r.name()) instanceof Ast.Data type && type.newtype()) {
            BindingId value = clauses.bindingsOf(type).get("value");
            if (value != null && terms.affineOf(bin, at, k) != null) {
                report(bin, type, bin.pos(), attempted,
                        verdictOf(r.name(), type, Map.of(value, bin), k, at, true));
            }
        }
    }

    /**
     * The verdict for one construction, over what each field is being given. A conditional never
     * reaches here: the walk opens it before anything is checked, so what a field is given is a
     * value and not a choice of two.
     */
    private Verdict verdictOf(Core.NewData nd, Ast.Data type, Known k, Denotations at) {
        Map<String, BindingId> fields = clauses.bindingsOf(type);
        Map<BindingId, Core> given = new HashMap<>();
        for (Core.FieldInit fi : nd.inits()) {
            BindingId field = fields.get(fi.name());
            if (field == null) {
                continue;
            }
            // A name given a value written out hands over that value: the clause folds over what
            // was written, wherever the writing was done.
            Core written = Terms.writtenValue(fi.value(), at);
            given.put(field, written != null ? written : fi.value());
        }
        return verdictOf(nd.typeName(), type, given, k, at, !constantlyBuilt(type, nd));
    }

    /** Which of the values a construction hands over is not one a clause may be read against
     * ({@link Terms#siteKey}) — by identity, since it is these very values that stand in the clause. */
    private Set<Core> unnamed(Collection<Core> given, Known k, Denotations at) {
        Set<Core> out = Collections.newSetFromMap(new IdentityHashMap<>());
        for (Core value : given) {
            if (terms.siteKey(value, at, k) == null) {
                out.add(value);
            }
        }
        return out;
    }

    /**
     * How a construction came out. A construction is checked before it is reported so that one
     * written over a conditional can be checked on each branch and answered once — which of the two
     * values it is is not decided here, so what holds of the construction is what holds of both.
     */
    private enum Verdict {
        /** Every clause is discharged, or none of them is expressible. */
        PROVED,
        /** A clause is expressible and unproven: the construction may abort. */
        UNKNOWN,
        /** A clause the reading without the path's assumptions already refutes, so the invariant
         * fails wherever the construction is written. */
        REFUTED_ALONE,
        /** A clause the full reading refutes and that reading does not. Something known here beyond
         * the values themselves settled it; which of the things known here is not asked, so this
         * does not say a condition on the path was one of them. */
        REFUTED_NOT_ALONE;

        boolean refuted() {
            return this == REFUTED_ALONE || this == REFUTED_NOT_ALONE;
        }

        /**
         * What holds of a value that is one of two. It is discharged where both are, and it is proven
         * to fail only where both fail — a construction one branch satisfies does not definitely
         * violate, whichever branch is taken. Everything else is possible and unproven.
         *
         * <p>Where both fail and only one of them fails on the values alone, the two together are
         * said not to: what is claimed of the construction is what the weaker of the two readings
         * supports. The other direction is the clauses of one invariant, which are conjoined rather
         * than alternative and are combined at {@link #verdictOf} the other way round.
         *
         * <p>A branch nothing reaches finds nothing to combine: {@link #reading} answers it with no
         * findings at all, and a position only one branch found is read as discharged on the other.
         */
        static Verdict of(Verdict a, Verdict b) {
            if (a == b) {
                return a;
            }
            return a.refuted() && b.refuted() ? REFUTED_NOT_ALONE : UNKNOWN;
        }
    }

    /** The discharge verdict for a construction of {@code type} whose fields are being given
     * {@code given}. */
    private Verdict verdictOf(TypeName named, Ast.Data type, Map<BindingId, Core> given, Known k,
                              Denotations at, boolean decidesFalse) {
        // What the construction hands over that no clause may be read against. A clause naming one of
        // them is left to the run-time check, and one that is decided outright is still decided: what
        // cannot be guarded is not the same as what cannot be computed.
        Set<Core> unnamed = unnamed(given.values(), k, at);
        List<Predicates.Clause> owed = new ArrayList<>();
        // A newtype construction from a value written out is the constant check's to report: it names
        // the clause that failed. It reads the construction as written, so a name given the value is
        // not one it sees, and this check says it instead — which is what `decidesFalse` carries.
        for (Core stated : clauses.statedAt(named, type, given)) {
            List<Predicates.Clause> o = predicates.obligations(stated, k, at, unnamed, decidesFalse);
            if (o != null) {
                owed.addAll(o);
            }
        }
        if (owed.isEmpty()) {
            return Verdict.PROVED;   // nothing here is expressible — the run-time check stands for it
        }
        NumericDomain dom = k.numbers();
        // The same clauses read against the same site, under what would be known here had no
        // condition on the path settled anything. What each clause states of the sizes it names holds
        // either way, so both readings take it.
        NumericDomain alone = k.unguarded().numbers();
        for (Predicates.Clause c : owed) {
            for (Predicates.Constraint known : c.known()) {
                dom = dom.assume(known.form(), known.rel());
                alone = alone.assume(known.form(), known.rel());
            }
        }
        // An invariant is the conjunction of its clauses, so every one of them is read before what
        // the invariant came out as is decided. A clause the values alone refute is the whole
        // invariant refuted on the values alone, whatever another clause needed to be refuted —
        // stopping at the first refutation would answer with whichever clause was declared first.
        boolean alongside = false;
        boolean unknown = false;
        for (Predicates.Clause c : owed) {
            if (c.dischargedBy(dom, k.facts())) {
                continue;
            }
            if (!c.refutedBy(dom, k.facts())) {
                unknown = true;
                continue;
            }
            if (c.refutedBy(alone, k.unguarded().facts())) {
                return Verdict.REFUTED_ALONE;
            }
            alongside = true;
        }
        if (alongside) {
            return Verdict.REFUTED_NOT_ALONE;
        }
        return unknown ? Verdict.UNKNOWN : Verdict.PROVED;
    }

    /** Whether the constant check reads this construction: a newtype's, over a value written where
     * it is built. That check names the clause that failed, so it is left to say it — and it reads
     * the construction as written, so a name given the value is not one it sees. */
    private static boolean constantlyBuilt(Ast.Data type, Core.NewData nd) {
        return type.newtype() && nd.inits().size() == 1 && Terms.isWritten(nd.inits().get(0).value());
    }

    /** Says what {@code verdict} found. A definite violation is an error and an unproven one a
     * warning; a discharged or non-expressible invariant says nothing. An {@code attempted}
     * construction raises no warning: what the warning reports is a possible abort, and an attempt
     * takes its else branch instead. */
    private void report(Core at, Ast.Data type, SourcePos pos, boolean attempted, Verdict verdict) {
        if (capturing != null) {
            capturing.found().put(new Occurrence(asWritten(at)),
                    new Reported(type, pos, verdict, attempted));
            return;
        }
        switch (verdict) {
            case REFUTED_ALONE -> reportViolation(type, pos, "check.invariant.violation.alone");
            case REFUTED_NOT_ALONE ->
                    reportViolation(type, pos, "check.invariant.violation.assumed");
            case UNKNOWN -> {
                if (!attempted) {
                    warnings.add(Diagnostic.of(DiagnosticCode.E2011, "check.invariant.unproven").at(pos).args(type.name())
                            .hint("check.invariant.reify", type.name()).warning().build());
                }
            }
            case PROVED -> { }
        }
    }

    /** What a construction came out as where it is being read on a branch rather than said. */
    private record Reported(Ast.Data type, SourcePos pos, Verdict verdict, boolean attempted) {}

    /**
     * Which construction a reading found: the one in the body as it was written. A reading is that
     * body with a conditional replaced, so the constructions along the way to the replacement are
     * rebuilt — those are the same construction given a different value, and they answer together.
     * One written inside the replacement is only in the reading that reached it, and one beside it
     * is the very node, unchanged.
     */
    private record Occurrence(Core of) {

        @Override
        public boolean equals(Object other) {
            return other instanceof Occurrence x && x.of == of;
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(of);
        }
    }

    /** What each node a rewrite built stands for, so a construction keeps its identity through one. */
    private final Map<Core, Core> rebuilt = new IdentityHashMap<>();

    /** The node {@code e} was built from, however many rewrites ago. */
    private Core asWritten(Core e) {
        Core from = e;
        Core next;
        while ((next = rebuilt.get(from)) != null) {
            from = next;
        }
        return from;
    }

    /**
     * Where a walk is reading one branch, what it finds is collected here rather than said. A body
     * read on each branch of a conditional reads every construction after it once per branch, and one
     * construction is one answer: it is the branches together that decide, the same as for a
     * construction the conditional is written inside.
     */
    private Capture capturing;

    /** What a reading has found so far. */
    private record Capture(Map<Occurrence, Reported> found) {

        static Capture empty() {
            return new Capture(new LinkedHashMap<>());
        }
    }

    /** What reading {@code e} finds, or nothing where the conditions along the way contradict — a
     * branch nothing reaches finds nothing, and what is not there violates nothing. */
    private Map<Occurrence, Reported> reading(Core e, Known k, Denotations at, int depth) {
        if (k.numbers().isBottom()) {
            return Map.of();
        }
        Capture outer = capturing;
        Capture mine = Capture.empty();
        capturing = mine;
        try {
            walk(e, k, at, depth + 1);
        } finally {
            capturing = outer;
        }
        return mine.found();
    }

    /**
     * The first conditional {@code e} gives a value to, or {@code null} where it gives none. A
     * conditional in tail position — an {@code if}'s own branches, a {@code let}'s body, a case's
     * body — is where the walk goes next rather than a value it is handed, and a closure's body is
     * read where the closure is applied.
     */
    private static Core.If conditionalValueIn(Core e) {
        return switch (e) {
            // Where the walk goes next is not a value it is handed: an `if`'s own branches, a `let`'s
            // body and a case's body are read after this, each with what is known there.
            case Core.If iff -> conditionalIn(iff.cond());
            case Core.IfConstructed ic -> conditionalIn(ic.construct());
            case Core.LetIn li -> conditionalIn(li.value());
            case Core.Match m -> conditionalIn(m.scrutinee());
            default -> conditionalIn(e);
        };
    }

    /** The first conditional inside a value. Everything under one is part of it, including the body
     * of a binding an expansion introduced — {@code let $0 = r in if $0.a > b then ...} is a helper
     * called on an argument, which is one value however many bindings writing it took. */
    private static Core.If conditionalIn(Core e) {
        if (e instanceof Core.If iff) {
            return iff;
        }
        if (e instanceof Core.Block) {
            return null;   // read where the closure is applied
        }
        Core.If[] found = {null};
        Core.forEachChild(e, child -> {
            if (found[0] == null) {
                found[0] = conditionalIn(child);
            }
        });
        return found[0];
    }

    /**
     * {@code e} with every occurrence of {@code was} replaced by {@code becomes}. Occurrence is by
     * what it computes and not by where it is written: an author who writes one conditional twice —
     * once to guard on and once to build from — wrote one value, and reading the two as two would
     * make the guard say nothing about what is built.
     */
    private Core without(Core e, Set<Core> was, Core becomes) {
        if (was.contains(e)) {
            return becomes;
        }
        if (e instanceof Core.Block) {
            return e;
        }
        Core made = Core.mapAll(e, child -> without(child, was, becomes), name -> name);
        if (made != e) {
            rebuilt.put(made, e);
            // What an attempt tries to build is rebuilt through the construction slot, which does not
            // come back through here, so its rebuild is recorded here instead. Unrecorded, the two
            // readings key one construction under two occurrences, and the branch that refutes it is
            // said on its own rather than answered by the branch that proves it.
            if (made instanceof Core.IfConstructed x && e instanceof Core.IfConstructed from
                    && x.construct() != from.construct()) {
                rebuilt.put(x.construct(), from.construct());
            }
        }
        return made;
    }

    /** Every conditional in {@code e} that computes what {@code value} computes, {@code value}
     * included. Asked once for the two readings, since which nodes those are does not depend on which
     * branch is being read. */
    private Set<Core> sameConditional(Core e, Core.If value, Denotations at) {
        Set<Core> alike = Collections.newSetFromMap(new IdentityHashMap<>());
        alike.add(value);
        String key = terms.bodyKey(value, at);
        if (key != null) {
            collectAlike(e, key, at, alike);
        }
        return alike;
    }

    private void collectAlike(Core e, String key, Denotations at, Set<Core> alike) {
        if (e instanceof Core.Block) {
            return;
        }
        if (e instanceof Core.If && key.equals(terms.bodyKey(e, at))) {
            alike.add(e);
            return;
        }
        Core.forEachChild(e, child -> collectAlike(child, key, at, alike));
    }

    /** Says of each construction the two readings reached what the two of them together decide. One
     * that only one reading reached is discharged on the other: it is not there to violate anything. */
    private void say(Map<Occurrence, Reported> a, Map<Occurrence, Reported> b) {
        Set<Occurrence> at = new LinkedHashSet<>(a.keySet());
        at.addAll(b.keySet());
        for (Occurrence one : at) {
            Reported x = a.get(one);
            Reported y = b.get(one);
            if (x == null || y == null) {
                // Written inside one branch, so the other reading did not discharge it — it was not
                // there to discharge. What the reading that reached it found is what it is.
                Reported said = x != null ? x : y;
                report(one.of(), said.type(), said.pos(), said.attempted(), said.verdict());
                continue;
            }
            report(one.of(), x.type(), x.pos(), x.attempted(),
                    Verdict.of(x.verdict(), y.verdict()));
        }
    }

    /** Reports the violation, saying it in the terms {@code reason} was reached in: the value alone
     * fails the invariant on its own, or it fails under what else is known where it stands. The check
     * knows which of the two decided it and not what within the second did, so neither message names
     * a guard. */
    private void reportViolation(Ast.Data type, SourcePos pos, String reason) {
        errors.add(CompileException.of(
                Diagnostic.of(DiagnosticCode.E2010, reason)
                        .at(pos).args(type.name()).build(),
                "constructing `" + type.name() + "` here violates its invariant"));
    }

    // --- introducing a binding -----------------------------------------------------------------

    /**
     * What entering a binding leaves the walk holding. Two environments, updated by one transition:
     * a value's place and what is known of it are separate questions with separate readers, and
     * introducing a location answers both at once. Returning only one of them is what let a binding
     * be named without being seeded.
     */
    private record Entered(Known known, Denotations at) {}

    /**
     * Introduces {@code root} as a location: somewhere nothing else names, holding a value of its
     * type. Entering it and seeding it are one act, so there is no state where the check names a
     * place it knows nothing about — which is a clause owed with nothing to establish it, and a
     * warning an author cannot clear.
     *
     * <p>Every value the walk reaches this way was built through its type's checked constructor, so
     * what that type guarantees holds of it. That is the same argument for a behavior's parameter,
     * for what a {@code match} arm binds, and for what a combinator hands its closure — one rule,
     * asked here.
     */
    private Entered enter(Core.Read root, Known known, Denotations at) {
        Denotations next = at.location(root.binding());
        return new Entered(seedAt(root, known, next, 0), next);
    }

    // --- seeding -------------------------------------------------------------------------------

    /**
     * Seeds the check with what the type of the value at {@code root} guarantees: a numeric newtype's
     * own invariant on its value, a predicate its invariant states of it, or a product data's
     * invariant over its fields (and one level of fields), each read at that very value. Sound by
     * closed construction — a value of type T was built through T's checked constructor.
     *
     * <p>Which is the same reading a construction gets, over field reads instead of field values: the
     * clause is the declaration's either way, and where it is established and where it is owed differ
     * only in direction.
     */
    private Known seedAt(Core root, Known k, Denotations at, int depth) {
        if (depth > FIELDS_SEEDED || !(root.type() instanceof Type.Ref ref)
                || !(symbols.get(ref.name()) instanceof Ast.Data data)) {
            return k;
        }
        Map<String, Type> fields = clauses.fieldsOf(data);
        Map<String, BindingId> bindings = clauses.bindingsOf(data);
        Map<BindingId, Core> given = new HashMap<>();
        fields.forEach((name, type) -> {
            BindingId field = bindings.get(name);
            if (field != null) {
                given.put(field, new Core.FieldAccess(root, name, type, root.pos()));
            }
        });
        Known out = k;
        List<Quantified> quantified = new ArrayList<>();
        for (Core stated : clauses.statedAt(ref.name(), data, given)) {
            predicates.quantifiedBy(stated, at, true, quantified);
            out = predicates.assume(predicates.obligations(stated, out, at, false), out,
                    Known.Held.OF_THE_VALUE);
        }
        out = out.and(quantified);
        if (data.newtype()) {
            // A newtype's `.value` is the same location as the newtype, so what its base guarantees is
            // guaranteed of this very atom: `data Outer = Inner` carries Inner's invariant.
            Core value = given.get(bindings.get("value"));
            return value == null ? out : seedAt(value, out, at, depth + 1);
        }
        for (Core value : given.values()) {
            out = seedAt(value, out, at, depth + 1);
        }
        return out;
    }

}
