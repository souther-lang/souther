package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.check.Combinators.Handed;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
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

    /**
     * What one analysis came to.
     *
     * <p>{@code status} is not about the model. It says whether the findings are all of the findings
     * there were: this check is fail-open, so an analysis that fell over produces exactly what an
     * analysis that finished and found nothing produces, and a consumer reading only the two lists
     * cannot tell them apart. Production does not need to — the run-time check is the backstop
     * either way — but a test asserting that a construction is discharged is asserting something
     * about an analysis that ran, and without this it would pass just as well on one that did not.
     */
    record Findings(List<CompileException> errors, List<Diagnostic> warnings, Status status) {}

    /** Whether an analysis produced all of the findings there were. {@code ABANDONED} covers both a
     * walk that fell over and a body there was none of: neither ran to the end, and the findings are
     * as complete in one case as in the other, which is not at all. */
    enum Status { COMPLETE, ABANDONED }

    /** One analysis that fell over, and what it fell over on. */
    record GaveUp(String where, RuntimeException why) {}

    /**
     * Where a test in this package reads the analyses that fell over, and null everywhere else.
     *
     * <p>Beside {@link #WATCHING} and for the same reason. Falling over is silent by design: the
     * catch that makes this check unable to reject a valid program also makes it unable to say it
     * stopped. A body with no discharge to run is not recorded here — there was nothing to fall over
     * on — so what lands here is only what the analysis could not get through.
     */
    static List<GaveUp> GAVE_UP;

    /** One construction and how this check came out on it. */
    record Said(String type, SourcePos pos, Verdict verdict) {}

    /**
     * Where a test in this package reads the verdicts a check reached, and null everywhere else.
     *
     * <p>What the check <em>says</em> is its findings, and a verdict is not one of them: two of the
     * four are silent, and which of those two a construction came out as is exactly what no
     * diagnostic reports. A test holding that difference has nowhere else to read it, and a
     * distinction nothing can read is one that stops being true without anything failing.
     */
    static List<Said> WATCHING;

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
    public static ClauseDischarge capabilityOf(Ast.Expr clause, SourcePos at, TypeName named,
                                               Ast.Data data, Symbols symbols) {
        InvariantChecker c = new InvariantChecker(symbols, Map.of());
        // Read over the declaration's own fields, each standing for itself: a construction hands one
        // value per field, so a clause naming a field names something wherever it is built. These
        // stand for a value rather than holding one, so they are entered as locations and nothing is
        // seeded of them — what a clause owes is the question, and answering it here would be
        // assuming it.
        Core stated = c.clauses.typed(clause, named, data);
        Denotations fields = Denotations.none()
                .locations(c.clauses.bindingsOf(named, data).values());
        Predicates.Owed owed;
        try {
            owed = stated == null ? Predicates.Owed.UNREADABLE
                    : c.predicates.obligations(stated, Known.top(), fields, false);
        } catch (RuntimeException why) {
            // Fail-open, as the walk is — and recorded, because a clause this could not read and an
            // analysis that fell over reading it both come out `runtimeOnly`, and only one of them
            // is something the model says.
            gaveUp("capabilityOf " + data.name(), why);
            owed = Predicates.Owed.UNREADABLE;
        }
        // A clause owing nothing is answered here as one nothing can be asked of. What it is instead
        // — a clause that holds wherever it is built — is a fourth answer this classification does
        // not have, and giving it one is a change to what the language states about a clause.
        if (owed.clauses().isEmpty()) {
            return ClauseDischarge.runtimeOnly(at, c.whyUnreadable(stated, fields));
        }
        for (Predicates.Clause owe : owed.clauses()) {
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
     * What the invariants reaching a value of {@code data} leave each of its fields able to hold, and
     * the atom each field is named by.
     *
     * <p>The same seeding a parameter of that type gets ({@link #seedAt}), read for its numbers
     * instead of for what it discharges. A record's own clause relates its fields; each field's type
     * bounds that field on its own; and both land in one domain over the same atoms, which is what
     * lets a bound reach one field through another.
     *
     * @param everyClauseRead whether every clause of the declaration was taken into the domain. False
     *                        where one could not be typed or held nothing this reads — the bounds are
     *                        then weaker than what the declaration actually says, and a caller
     *                        turning one into an obligation has to know that
     */
    record Seeded(NumericDomain numbers, Map<String, String> atoms, boolean everyClauseRead) {}

    /** {@link Seeded} for one declaration. Never throws: a declaration this cannot read is one whose
     * fields it says nothing about, which is the same answer as a declaration with no rules. */
    static Seeded seedFields(TypeName named, Ast.Data data, Symbols symbols) {
        return seedFields(named, data, symbols, Map.of());
    }

    /**
     * {@link Seeded} with some of the fields already settled at a value.
     *
     * <p>What is left for the others, given those. The same domain and the same closure — settling a
     * field is one more assertion into it — so what comes back is the range each remaining field can
     * still take, which is where a row completing that assignment has to look.
     */
    static Seeded seedFields(TypeName named, Ast.Data data, Symbols symbols,
                             Map<String, BigDecimal> settled) {
        InvariantChecker c = new InvariantChecker(symbols, Map.of());
        Map<String, Type> fields = c.clauses.fieldsOf(data);
        Map<String, BindingId> bindings = c.clauses.bindingsOf(named, data);
        Denotations at = Denotations.none().locations(bindings.values());
        Known k = Known.top();
        boolean read = true;
        try {
            for (Ast.InvariantClause clause : c.clauses.of(named, data)) {
                Core stated = c.clauses.typed(clause.expr(), named, data);
                if (stated == null) {
                    read = false;
                    continue;
                }
                Predicates.Owed owed = c.predicates.obligations(stated, k, at, false);
                read &= !owed.unreadable();
                k = c.predicates.assume(owed, k, Known.Held.OF_THE_VALUE);
            }
            // And what each field's own type says of it, at the field's own location. A depth of one
            // is already spent on the record, so this reaches the field's newtype and stops where the
            // seeding of a parameter would.
            for (Map.Entry<String, BindingId> field : bindings.entrySet()) {
                Type type = fields.get(field.getKey());
                if (type != null) {
                    // No depth limit here: this is the reading a boundary is derived from, and a
                    // rule the construction must satisfy is a rule wherever in the value it sits.
                    k = c.seedAt(new Core.Read(field.getKey(), field.getValue(), type, NOWHERE),
                            k, at, 1, Integer.MAX_VALUE, new HashSet<>());
                }
            }
        } catch (RuntimeException why) {
            gaveUp("seedFields " + named.name(), why);
            return new Seeded(NumericDomain.top(), Map.of(), false);
        }
        Map<String, String> atoms = new LinkedHashMap<>();
        Map<String, Type> typeAt = new LinkedHashMap<>();
        for (Map.Entry<String, BindingId> field : bindings.entrySet()) {
            Type type = fields.get(field.getKey());
            if (type != null) {
                c.name(new Core.Read(field.getKey(), field.getValue(), type, NOWHERE),
                        field.getKey(), type, at, k, symbols, 1, atoms, typeAt);
            }
        }
        NumericDomain numbers = k.numbers();
        for (Map.Entry<String, BigDecimal> each : settled.entrySet()) {
            String atom = atoms.get(each.getKey());
            Type type = typeAt.get(each.getKey());
            if (atom == null || type == null) {
                continue;
            }
            numbers = numbers.assume(
                    NumericDomain.LinearForm.atom(atom)
                            .minus(NumericDomain.LinearForm.constant(each.getValue())),
                    NumericDomain.Rel.EQ,
                    Map.of(atom, c.terms.granularityOf(type)));
        }
        return new Seeded(numbers, atoms, read);
    }

    /**
     * The atom each position under {@code value} is named by, keyed by the path it is reached at.
     *
     * <p>The walk {@link #seedAt} took, over the same reads, so a position the seeding put a bound on
     * is a position this can name. Two levels down as well as one: a clause on a record relates a
     * field of a field to something, and the bound that leaves on it is read at the path it sits at
     * rather than at the record it happens to be inside.
     */
    private void name(Core value, String path, Type type, Denotations at, Known k, Symbols symbols,
                      int depth, Map<String, String> atoms, Map<String, Type> typeAt) {
        String atom = terms.atomOf(value, at, k);
        if (atom != null) {
            atoms.put(path, atom);
            typeAt.put(path, type);
        }
        if (depth > FIELDS_SEEDED || !(type instanceof Type.Ref ref)
                || !(symbols.get(ref.name()) instanceof Ast.Data data) || data.newtype()) {
            return;
        }
        for (Map.Entry<String, Type> field : clauses.fieldsOf(data).entrySet()) {
            name(new Core.FieldAccess(value, field.getKey(), field.getValue(), NOWHERE),
                    path + "." + field.getKey(), field.getValue(), at, k, symbols, depth + 1,
                    atoms, typeAt);
        }
    }

    /**
     * Whether every rule reaching a value of {@code data} is one the numeric domain reasons over.
     *
     * <p>{@link ClauseDischarge.Kind#DERIVABLE} is the same classification a construction is judged
     * by, asked here of the declaration rather than of a site. A clause that is only nameable — a
     * pattern, a membership — narrows no bound, and a clause outside the fragment narrows none
     * either; both leave a way the record refuses a value that the bounds do not express.
     *
     * <p>The same reach the seeding has, so what this classifies is what that took in.
     */
    /**
     * Whether every rule that can refuse a value of {@code data} was read as a bound.
     *
     * <p>Asked over the values a construction has to produce, which is not the depth a report takes a
     * value apart to. {@code FIELDS_SEEDED} and {@code MAX_DEPTH} are limits on how far a measurement
     * is worth carrying; a rule four records down refuses the outermost construction exactly as one
     * on its own fields does, so a bound at the top is promised by nothing while that rule is unread.
     *
     * <p>Down the required chain only. A field that is optional or a collection can be absent or
     * empty, so a rule inside it is a rule about a value the construction need not make. A type
     * already met is not entered again, which is what stops a record that holds itself.
     */
    static boolean everyRuleRead(TypeName named, Ast.Data data, Symbols symbols) {
        return everyRuleRead(named, data, symbols, new HashSet<>());
    }

    private static boolean everyRuleRead(TypeName named, Ast.Data data, Symbols symbols,
                                         Set<TypeName> seen) {
        if (!seen.add(named)) {
            return true;
        }
        if (data.newtype()) {
            if (!everyRuleBecameABound(named, data, symbols)) {
                return false;
            }
        } else {
            for (Ast.InvariantClause clause : TypeOps.effectiveInvariants(data, symbols)) {
                if (capabilityOf(clause.expr(), clause.pos(), named, data, symbols).kind()
                        != ClauseDischarge.Kind.DERIVABLE) {
                    return false;
                }
            }
        }
        for (Type type : TypeOps.fieldTypes(data, symbols).values()) {
            if (type instanceof Type.Ref ref && symbols.get(ref.name()) instanceof Ast.Data inner
                    && !everyRuleRead(ref.name(), inner, symbols, seen)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether every rule on a newtype became one of the constraints its bounds are read from.
     *
     * <p>The same reader, so the same answer: a conjunct that gave the position a bound was read, and
     * one that gave none — {@code isOdd(value)} beside {@code value >= 0} — is a way the type refuses
     * a value that the bounds do not express.
     *
     * <p>Which reader that is depends on what the value is carried as. A number's range comes from
     * the comparison itself; anything else — a length, a pattern, a size — is read as the runtime
     * check it becomes, which is the only reading of those there is.
     */
    private static boolean everyRuleBecameABound(TypeName named, Ast.Data data, Symbols symbols) {
        Type carried = TypeOps.numericBase(Type.ref(named), symbols);
        Type base = carried != null ? carried : TypeOps.fieldTypes(data, symbols).get("value");
        // Every name the value wears, read against what it is carried as. Asking only the outermost
        // one leaves a rule a layer down unaccounted for, and reading it against the type that layer
        // declares rather than against the number underneath makes every such rule unreadable.
        for (TypeOps.Layer layer : TypeOps.newtypeChain(Type.ref(named), symbols)) {
            for (Ast.InvariantClause clause : TypeOps.effectiveInvariants(layer.data(), symbols)) {
                boolean numeric = base == Type.INT || base == Type.DECIMAL;
                for (Ast.Expr each
                        : souther.compiler.codegen.InvariantConstraints.clauses(clause.expr())) {
                    boolean read = numeric ? InvariantBound.of(each, base).isPresent()
                            : souther.compiler.codegen.InvariantConstraints.of(each, base).isPresent();
                    if (!read) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /** A position read from no source, for the reads this makes to stand at. */
    private static final SourcePos NOWHERE = new SourcePos(0, 0);

    /**
     * Analyzes one behavior body against the bindings its inputs are. Never throws. A {@code null}
     * body is one the analysis representation could not be built or typed for, and is not analyzed at
     * all.
     */
    static Findings analyze(Core body, Map<TypeName, List<Ast.InvariantClause>> invariants,
                            Scope params, Symbols symbols) {
        InvariantChecker c = new InvariantChecker(symbols, invariants);
        if (body == null) {
            return new Findings(c.errors, c.warnings, Status.ABANDONED);
        }
        try {
            Entered in = new Entered(Known.top(), Denotations.none());
            for (Map.Entry<BindingId, Scope.Binding> p : params.bindings().entrySet()) {
                in = c.enter(new Core.Read(p.getValue().name(), p.getKey(), p.getValue().type(),
                        body.pos()), in.known(), in.at());
            }
            c.walk(body, in.known(), in.at(), 0);
        } catch (RuntimeException why) {
            // fail-open: the run-time invariant check remains the backstop
            gaveUp("analyze", why);
            return new Findings(c.errors, c.warnings, Status.ABANDONED);
        }
        return new Findings(c.errors, c.warnings, Status.COMPLETE);
    }

    /** Records an analysis that fell over, for a test in this package to read. */
    private static void gaveUp(String where, RuntimeException why) {
        List<GaveUp> watching = GAVE_UP;
        if (watching != null) {
            watching.add(new GaveUp(where, why));
        }
    }

    // --- the walk ------------------------------------------------------------------------------

    private void walk(Core e, Known k, Denotations at, int depth) {
        ConditionalSite site = conditionalValueIn(e);
        if (site != null && depth < BRANCHES_OPENED) {
            // A conditional in a value position is one of its two branches, and which one is decided
            // by its condition. So this is read once with each standing there, under that condition,
            // and what the two readings find is said once. Every place a conditional can be given —
            // to a field, to a name, to a guard — is this one place.
            Core.If value = site.conditional();
            // Everything about the conditional is read where it stands, which is inside every binder
            // on the way down to it and not at the outer place the reading is decided on: what its
            // condition settles, and what the condition's own subtree is. Read at the outer place the
            // condition names binders nothing has entered, which denote nothing — it would settle
            // nothing, and a construction written inside it would be one nothing can be said of.
            Entered inside = scopeOf(site, k, at);
            Known within = inside.known();
            Denotations there = inside.at();
            walk(value.cond(), within, there, depth);
            Set<Core> alike = sameConditional(e, value, there);
            // The readings start from where the conditional stood, not from outside it. The tree each
            // is given still holds those binders and walks into them again, which is why entering one
            // already entered is nothing: a second transition would forget what the branch settled.
            say(reading(without(e, alike, value.then()),
                            predicates.assumeCond(value.cond(), within, there, true), there, depth),
                    reading(without(e, alike, value.els()),
                            predicates.assumeCond(value.cond(), within, there, false), there, depth));
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
                Entered in = bindLet(li, k, at);
                walk(li.body(), in.known(), in.at(), depth);
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
            BindingId value = clauses.bindingsOf(r.name(), type).get("value");
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
        Map<String, BindingId> fields = clauses.bindingsOf(nd.typeName(), type);
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
    enum Verdict {
        /** Every clause is discharged. */
        PROVED,
        /** A clause names something the check cannot read at this construction, and no clause is
         * unproven: nothing is owed here because nothing could be asked. Silent, as a discharge is,
         * and not the same thing — the run-time check is what stands for the clause, and an author
         * who reads the silence as a proof is reading something that was never attempted. */
        UNREPRESENTABLE,
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

        /** Whether the reading found nothing that may fail: every clause it could read is
         * discharged. Not the same question as whether anything is reported — what is reported is
         * settled at {@link #report}, and this is what the two readings of one construction are
         * combined by. */
        boolean holds() {
            return this == PROVED || this == UNREPRESENTABLE;
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
            if (a.refuted() && b.refuted()) {
                return REFUTED_NOT_ALONE;
            }
            // Neither reading found anything that may fail, and they are not the same reading: one
            // discharged the invariant and the other could not read it. So neither does this, and
            // what it is not is the invariant proven of both.
            return a.holds() && b.holds() ? UNREPRESENTABLE : UNKNOWN;
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
        // A clause the check cannot read here owes nothing and proves nothing, and the two are not
        // the same answer. Kept apart: a clause that owes nothing because it folded to what it is read
        // with is discharged, and one that owes nothing because nothing here could be asked of it is
        // left to the run-time check.
        boolean unreadable = false;
        // A newtype construction from a value written out is the constant check's to report: it names
        // the clause that failed. It reads the construction as written, so a name given the value is
        // not one it sees, and this check says it instead — which is what `decidesFalse` carries.
        for (Core stated : clauses.statedAt(named, type, given)) {
            Predicates.Owed o = predicates.obligations(stated, k, at, unnamed, decidesFalse);
            unreadable |= o.unreadable();
            owed.addAll(o.clauses());
        }
        if (owed.isEmpty()) {
            return unreadable ? Verdict.UNREPRESENTABLE : Verdict.PROVED;
        }
        NumericDomain dom = k.numbers();
        // The same clauses read against the same site, under what would be known here had no
        // condition on the path settled anything. What each clause states of the sizes it names holds
        // either way, so both readings take it.
        NumericDomain alone = k.unguarded().numbers();
        for (Predicates.Clause c : owed) {
            for (Predicates.Constraint known : c.known()) {
                Map<String, Granularity> kinds = terms.kindsOf(known.form());
                dom = dom.assume(known.form(), known.rel(), kinds);
                alone = alone.assume(known.form(), known.rel(), kinds);
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
        if (unknown) {
            return Verdict.UNKNOWN;
        }
        // Every clause that could be read is discharged. One that could not be read still stands, so
        // this is not the whole invariant proven.
        return unreadable ? Verdict.UNREPRESENTABLE : Verdict.PROVED;
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
        List<Said> watching = WATCHING;
        if (watching != null && capturing == null) {
            watching.add(new Said(type.name(), pos, verdict));
        }
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
            // Nothing was asked here, so nothing is said. Whether that is the right thing to say of a
            // construction the check could not read is a question about what E2011 reports, and this
            // answers it the way it has always been answered.
            case UNREPRESENTABLE -> { }
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
     * A conditional a value is handed, and the bindings in scope where it stands. The two go
     * together: a node is found by searching down from the outside, and what it means is settled by
     * where it was found, so a search that answered with the node alone would leave the reading to
     * work the scope out again — which is what it got wrong.
     *
     * <p>Every binder the search descends through is carried, and not only the ones a construction
     * outside could have been read against. What stands in scope decides two things: what the
     * condition settles about the value being built, and what the condition's own subtree means —
     * a construction written inside a condition is a construction like any other, and reading it
     * where its binders are not entered is reading it as something nothing can be said of.
     */
    private record ConditionalSite(Core.If conditional, List<Binder> scope) {

        /** One binder the conditional stands inside, as the environment its body is read in. */
        private interface Binder {
            Entered entering(InvariantChecker c, Known k, Denotations at);
        }

        /** The same site, read from outside {@code binder} — so {@code binder} is the outermost of
         * what it is inside. */
        ConditionalSite under(Binder binder) {
            List<Binder> outer = new ArrayList<>();
            outer.add(binder);
            outer.addAll(scope);
            return new ConditionalSite(conditional, List.copyOf(outer));
        }

        /** A {@code let}'s body, read with the name standing for what it was given. */
        static Binder of(Core.LetIn li) {
            return (c, k, at) -> c.bindLet(li, k, at);
        }

        /** A {@code match} arm's body, read with what the arm binds standing for a value of the
         * case's type — a location this arm introduces, carrying what that type guarantees. */
        static Binder of(Core.Case arm) {
            return (c, k, at) -> c.enter(Terms.read(arm.binding(), arm.bindType(), arm.pos()), k, at);
        }

        /** An attempted construction's success branch, read with the binding carrying the invariant
         * the attempt established. */
        static Binder of(Core.IfConstructed ic) {
            return (c, k, at) ->
                    c.enter(Terms.read(ic.binder(), ic.construct().type(), ic.pos()), k, at);
        }
    }

    /**
     * The first conditional {@code e} gives a value to, or {@code null} where it gives none. A
     * conditional in tail position — an {@code if}'s own branches, a {@code let}'s body, a case's
     * body — is where the walk goes next rather than a value it is handed, and a closure's body is
     * read where the closure is applied.
     */
    private static ConditionalSite conditionalValueIn(Core e) {
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

    /** The first conditional inside a value, with what it is inside. Everything under one is part of
     * it, including the body of a binding an expansion introduced — {@code let $0 = r in if $0.a > b
     * then ...} is a helper called on an argument, which is one value however many bindings writing
     * it took. Those bindings are what the conditional is read in the scope of; a binding is not in
     * scope for the value it is itself given, so a conditional found there is inside nothing. */
    private static ConditionalSite conditionalIn(Core e) {
        if (e instanceof Core.If iff) {
            return new ConditionalSite(iff, List.of());
        }
        if (e instanceof Core.Block) {
            return null;   // read where the closure is applied
        }
        if (e instanceof Core.LetIn li) {
            ConditionalSite given = conditionalIn(li.value());
            if (given != null) {
                return given;
            }
            ConditionalSite inside = conditionalIn(li.body());
            return inside == null ? null : inside.under(ConditionalSite.of(li));
        }
        if (e instanceof Core.Match m) {
            ConditionalSite asked = conditionalIn(m.scrutinee());
            if (asked != null) {
                return asked;
            }
            for (Core.Case arm : m.cases()) {
                ConditionalSite inside = conditionalIn(arm.body());
                if (inside == null) {
                    continue;
                }
                // A case that binds nothing introduces nothing: its body is read as the arm's own.
                return arm.binding() == null || arm.bindType() == null
                        ? inside : inside.under(ConditionalSite.of(arm));
            }
            return null;
        }
        if (e instanceof Core.IfConstructed ic) {
            ConditionalSite tried = conditionalIn(ic.construct());
            if (tried != null) {
                return tried;
            }
            ConditionalSite held = conditionalIn(ic.then());
            if (held != null) {
                return held.under(ConditionalSite.of(ic));
            }
            // A departure stands where the invariant did not hold and nothing was built, so it is
            // inside nothing the attempt would have guaranteed.
            for (Core.ElseArm arm : ic.els()) {
                ConditionalSite departed = conditionalIn(arm.body());
                if (departed != null) {
                    return departed;
                }
            }
            return null;
        }
        ConditionalSite[] found = {null};
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

    /**
     * Every conditional in {@code e} that computes what {@code value} computes, {@code value}
     * included. Asked once for the two readings, since which nodes those are does not depend on which
     * branch is being read.
     *
     * <p>{@code at} is where {@code value} stands, which is what keying it needs. A candidate
     * elsewhere in {@code e} is keyed there too rather than in its own scope, so two conditionals
     * that compute the same value under different bindings are read as two — which is the thing this
     * exists to prevent, still unanswered for that shape.
     */
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
        errors.add(CompileException.of(Diagnostic.of(DiagnosticCode.E2010, reason)
                        .at(pos).args(type.name()).build()));
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
     * The environment a binding's body is read in. Both places a body is read reach it through here:
     * the walk on its way into one, and a conditional hoisted out of one. The bug this answers came
     * from those two working the scope rule out separately, so there is one of it.
     *
     * <p>The initializer is not read here. The walk reads it before it gets here, and a hoisted
     * conditional was found past it.
     *
     * <p>The name is an alias for what its initializer denotes, so what is recorded about it is
     * recorded under that denotation and not under the binding. Recording it under the binding is
     * what made a named subexpression a term of its own, answering differently from the very
     * expression it was given.
     */
    private Entered bindLet(Core.LetIn li, Known k, Denotations at) {
        // Entering a binding the walk is already inside is not a second binding of it. A branch is
        // read from where its conditional stood, which is inside these, over a tree that still holds
        // them; running the transition again would assign the name its form a second time, and an
        // assignment forgets what was known of what it assigns to — including what the branch had
        // just established.
        if (at.valueOf(li.binder().id()) == li.value()) {
            return new Entered(k, at);
        }
        Denotes what = terms.denotationOf(li.value(), at, k);
        Known out = k;
        // A binding that denotes what it was given is an alias and introduces no value, so there is
        // nothing to record of it: what holds of what it names already holds. Recording it anyway
        // assigns that name its own form, and an assignment drops what was known of what it assigns
        // to — the bound on it would be lost to the copy. A location is always this; a term is where
        // the form is that term's own atom.
        if (what instanceof Denotes.Term term && terms.affineScalarBase(li.value().type()) != null) {
            LinearForm vf = terms.affineOf(li.value(), at, k);
            if (vf != null && !vf.equals(LinearForm.atom(term.key()))) {
                out = out.assigning(term.key(), vf,
                        terms.kindsOf(vf, term.key(), li.value().type()));
            }
        }
        return new Entered(out, at.binding(li.binder().id(), li.value(), what));
    }

    /** Where {@code site}'s conditional stands: {@code k} and {@code at} with every binder it is
     * inside entered, outermost first. */
    private Entered scopeOf(ConditionalSite site, Known k, Denotations at) {
        Entered in = new Entered(k, at);
        for (ConditionalSite.Binder binder : site.scope()) {
            in = binder.entering(this, in.known(), in.at());
        }
        return in;
    }

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
    Known seedAt(Core root, Known k, Denotations at, int depth) {
        return seedAt(root, k, at, depth, FIELDS_SEEDED, new HashSet<>());
    }

    /**
     * The same, as far as {@code limit} levels down, with the types on the way recorded.
     *
     * <p>How far to seed is not one number. What a walk over a body can afford to read of a
     * parameter is a cost bound and stops at {@code FIELDS_SEEDED}; what a construction has to
     * satisfy has no depth at all, since a rule four records down refuses the outermost value
     * exactly as one on the top does. A projection that stopped at two and was then classified by a
     * walk that did not would call a bound complete that a rule below it moves.
     *
     * <p>{@code onPath} is the types entered on the way here, so a record that holds another of its
     * own kind stops rather than descending for ever. Kept per path and not for the whole walk: two
     * fields of one type are two positions and both are seeded.
     */
    private Known seedAt(Core root, Known k, Denotations at, int depth, int limit,
                         Set<TypeName> onPath) {
        if (depth > limit || !(root.type() instanceof Type.Ref ref)
                || !(symbols.get(ref.name()) instanceof Ast.Data data)
                || !onPath.add(ref.name())) {
            return k;
        }
        Map<String, Type> fields = clauses.fieldsOf(data);
        Map<String, BindingId> bindings = clauses.bindingsOf(ref.name(), data);
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
            out = value == null ? out : seedAt(value, out, at, depth + 1, limit, onPath);
        } else {
            for (Core value : given.values()) {
                out = seedAt(value, out, at, depth + 1, limit, onPath);
            }
        }
        onPath.remove(ref.name());
        return out;
    }

}
