package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.check.BehaviorContract.Guard;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

/**
 * What holds where a walk stands, and the three acts that move it.
 *
 * <p>The rules and not the check. Introducing a binding, taking a condition as holding, and reading
 * what a type guarantees of a value are answers about a program, and the question they add up to —
 * can anything at all stand here — is asked by more than the check they were written for. Held
 * apart so that there is one reading of it: a second walk that threaded its own narrowing would be
 * a second set of rules, and the two would part company at the first clause a domain other than the
 * numbers has a word for ({@code value == "A"} beside {@code value /= "A"} reaches no number and
 * leaves the predicates contradictory).
 *
 * <p>Nothing here reports anything. What is done with an answer — a clause discharged, an
 * obligation left standing, an arm named as one nothing reaches — is the caller's, and each of them
 * wants a different one. An engine that also decided would settle those before either caller was
 * written.
 *
 * <p>Threaded functionally. Every act answers a new {@link Entered} and leaves what it was given as
 * it was, so a branch read under one condition says nothing about the branch beside it.
 */
final class PathEngine {

    /** How far into a value's fields the seeding reads. A type's own invariant is what its fields
     * guarantee, and a field's type carries its own; past a couple of levels what a clause could be
     * read against is a value the body would have had to name, and it names it by reading it. */
    static final int FIELDS_SEEDED = 2;

    private final Symbols symbols;
    /** The declarations' invariants, typed where they are declared and read where a value is built. */
    private final Clauses clauses;
    /** Where a value is, what it is called, and what can be said of it. */
    private final Terms terms;
    /** What a clause owes and what a guard settles. */
    private final Predicates predicates;
    /** What each behavior a body may call states about its answer, by the name it is called under. */
    private final Map<ValueName.Behavior, StatedContract> contracts;

    PathEngine(Symbols symbols, Map<TypeSymbol, List<Hir.InvariantClause>> dischargeInvariants) {
        this(symbols, dischargeInvariants, Map.of(), Terms.Of.THE_DISCHARGE_TREE);
    }

    PathEngine(Symbols symbols, Map<TypeSymbol, List<Hir.InvariantClause>> dischargeInvariants,
               Map<ValueName.Behavior, StatedContract> contracts) {
        this(symbols, dischargeInvariants, contracts, Terms.Of.THE_DISCHARGE_TREE);
    }

    /**
     * The same rules, told which tree they are being read over.
     *
     * <p>The rules do not change with the tree; what changes is what a shape they cannot name means.
     * Over the tree that runs, {@code List.map} is the fold it lowers to, and a reading that
     * recorded the fold as a shape this compiler has no term for would be answering about the
     * representation under the name of a gap.
     */
    PathEngine(Symbols symbols, Map<TypeSymbol, List<Hir.InvariantClause>> dischargeInvariants,
               Terms.Of reading) {
        this(symbols, dischargeInvariants, Map.of(), reading);
    }

    PathEngine(Symbols symbols, Map<TypeSymbol, List<Hir.InvariantClause>> dischargeInvariants,
               Map<ValueName.Behavior, StatedContract> contracts, Terms.Of reading) {
        this.symbols = symbols;
        this.clauses = new Clauses(symbols, dischargeInvariants);
        this.terms = new Terms(symbols, reading);
        this.predicates = new Predicates(terms);
        this.contracts = Map.copyOf(contracts);
    }

    Symbols symbols() {
        return symbols;
    }

    Clauses clauses() {
        return clauses;
    }

    Terms terms() {
        return terms;
    }

    Predicates predicates() {
        return predicates;
    }

    /**
     * A place and what is known of it, answered together.
     *
     * <p>Both halves or neither: a value's place and what is known of it are separate questions with
     * separate readers, and introducing a location answers both at once. Returning only one of them
     * is what let a binding be named without being seeded.
     */
    record Entered(Known known, Denotations at) {

        static Entered nothing() {
            return new Entered(Known.top(), Denotations.none());
        }
    }

    // --- the three acts ------------------------------------------------------------------------

    /**
     * Introduces {@code root} as a location: somewhere nothing else names, holding a value of its
     * type. Entering it and seeding it are one act, so there is no state where a reading names a
     * place it knows nothing about — which is a clause owed with nothing to establish it, and a
     * warning an author cannot clear.
     *
     * <p>Every value a walk reaches this way was built through its type's checked constructor, so
     * what that type guarantees holds of it. That is the same argument for a behavior's parameter,
     * for what a {@code match} arm binds, and for what a combinator hands its closure — one rule,
     * asked here.
     */
    Entered enter(Core.Read root, Known known, Denotations at) {
        Denotations next = at.location(root.binding());
        return new Entered(seedAt(root, known, next, 0), next);
    }

    /**
     * The environment a binding's body is read in. Every place a body is read reaches it through
     * here: a walk on its way into one, and a conditional hoisted out of one. The bug this answers
     * came from those working the scope rule out separately, so there is one of it.
     *
     * <p>The initializer is not read here. A walk reads it before it gets here, and a hoisted
     * conditional was found past it.
     *
     * <p>The name is an alias for what its initializer denotes, so what is recorded about it is
     * recorded under that denotation and not under the binding. Recording it under the binding is
     * what made a named subexpression a term of its own, answering differently from the very
     * expression it was given.
     *
     * <p>Nothing is recorded of the name itself. A name is read as the expression it was given —
     * {@link Terms#affine} reads through it, and reads through a field taken off it the same way —
     * so there is no second reading for a fact about the name to be needed by. Recording one meant
     * giving the name's own atom the bounds of the form it was given, which is what a guard read one
     * way and a construction read the other had between them, and a bound is not a relation: it left
     * the guard settling nothing about the construction (#676).
     */
    Entered bindLet(Core.LetIn li, Known k, Denotations at) {
        // Entering a binding a walk is already inside is not a second binding of it. A branch is
        // read from where its conditional stood, which is inside these, over a tree that still holds
        // them.
        if (at.valueOf(li.binder().id()) == li.value()) {
            return new Entered(k, at);
        }
        Denotes what = terms.denotationOf(li.value(), at, k);
        return new Entered(k, at.binding(li.binder().id(), li.value(), what));
    }

    /**
     * {@code k} with {@code cond} taken as holding, or as failing where {@code positive} is false —
     * and whether any of it was taken in at all.
     *
     * <p>Sound where the condition is of a shape no rule here reads: what cannot be taken in is
     * left out, and a reading that took nothing in is one that ruled nothing out. Which of those
     * happened is the second half of the answer, because the state alone cannot say: a condition
     * nothing could read and one read to no effect leave it identical.
     */
    Predicates.Assumed assuming(Core cond, Known k, Denotations at, boolean positive) {
        return predicates.assumeCond(cond, k, at, positive);
    }

    /**
     * What a {@code match} arm's body is read under.
     *
     * <p>A sum has no fields of its own, so the scrutinee is not a location any clause could have
     * named — the case's value names only itself. What the arm binds is a value of the case's type,
     * reached only here, so it is a location this arm introduces and it carries what that type
     * guarantees.
     *
     * <p>An arm that binds nothing introduces nothing, and its body is read as the arm's own. Held
     * here rather than at each walk: two readings deciding it apart is two chances to forget, and
     * the one that forgot fell over on every ordinary unit case.
     */
    Entered enteringArm(Core.Case arm, Core scrutinee, Known k, Denotations at) {
        Entered in = arm.binding() == null || arm.bindType() == null
                ? new Entered(k, at)
                : enter(Terms.read(arm.binding(), arm.bindType(), arm.pos()), k, at);
        return assuming(answeredBy(scrutinee, in.at()), answered(arm, scrutinee),
                guard -> impliedBy(guard, arm.pattern()), in);
    }

    /**
     * The same arm, where the answer it is opening came from nowhere this can name.
     *
     * <p>Kept as the shorter question a caller with no scrutinee to hand asks — a conditional lifted
     * out of a body is read where it stood, and what it stood in front of is not being re-decided
     * here.
     */
    Entered enteringArm(Core.Case arm, Known k, Denotations at) {
        return enteringArm(arm, null, k, at);
    }

    // --- what a call's answer was declared to be ------------------------------------------------

    /**
     * What the behavior that produced {@code value} states about its answer, or null where nothing
     * did.
     *
     * <p>The call is followed through the names it was given. {@code let r = findTodo(id)} and
     * {@code match findTodo(id)} are the same program to an author, and asking whether the scrutinee
     * <em>is</em> a call answers only the second — the binding it went through is not a step away
     * from the call, it is a name for it. Derived from what the walk already recorded rather than
     * remembered beside it: {@link Denotations} holds what each binding was given, and holding an
     * origin as well would be two records of one fact to keep agreeing.
     */
    private Answered answeredBy(Core value, Denotations at) {
        Core.Call call = value == null ? null : originatingCall(value, at, new HashSet<>());
        if (call == null || !(call.fn() instanceof Core.Reached reached)
                || !(reached.denotes() instanceof ValueName.Behavior behavior)) {
            return null;
        }
        StatedContract stated = contracts.get(behavior);
        return stated == null ? null : new Answered(stated, call);
    }

    /** An answer and what was declared about it: the rules, and the call they are read at — a rule
     * names the behavior's own parameters, and what those are here is what this call handed over. */
    private record Answered(StatedContract stated, Core.Call call) {}

    /** The call {@code value} came from, through however many names it was given, or null where it
     * came from something else. {@code seen} stops a binding given itself. */
    private Core.Call originatingCall(Core value, Denotations at, Set<BindingId> seen) {
        if (value instanceof Core.Call call) {
            return call;
        }
        if (value instanceof Core.Read read && seen.add(read.binding())) {
            Core given = at.valueOf(read.binding());
            return given == null ? null : originatingCall(given, at, seen);
        }
        return null;
    }

    /**
     * Whether an arm's pattern says the answer is what {@code guard} is about.
     *
     * <p>Read off the pattern, which is the proof the checker already has: an arm is taken because
     * the value is one of the cases it names, so an arm naming one case says the answer is that case
     * and an arm naming several says only that it is one of them. A rule about one of several is a
     * rule about a value this arm may not have.
     *
     * <p>A rule under no case applies to every answer, so any arm reaching it is an arm it holds of.
     */
    private static boolean impliedBy(Guard guard, Core.ResolvedPattern pattern) {
        if (guard instanceof Guard.Always) {
            return true;
        }
        if (!(guard instanceof Guard.Case(CaseSelector selector))
                || !(pattern instanceof Core.ResolvedPattern.Single single)) {
            return false;
        }
        return single.selector().name().equals(selector.name());
    }

    /** What the arm holds of the answer: what it binds where it binds one, and the answer itself
     * where it does not — an arm may state a relation about a case that carries nothing. */
    private static Core answered(Core.Case arm, Core scrutinee) {
        return arm.binding() == null || arm.bindType() == null ? scrutinee
                : Terms.read(arm.binding(), arm.bindType(), arm.pos());
    }

    /**
     * {@code in} with every rule the arm's pattern implies taken as holding of the answer.
     *
     * <p>Conjunct by conjunct, as everything else about a clause is. A rule one half of which names
     * something this cannot read still says the other half: dropping the rule for the half that got
     * away would leave a caller with less than the declaration gives them, and taking the half that
     * was read is what the seeding does everywhere else.
     */
    private Entered assuming(Answered answered, Core answer, Predicate<Guard> reached, Entered in) {
        if (answered == null || answer == null) {
            return in;
        }
        Known out = in.known();
        for (StatedContract.StatedRule rule : answered.stated().rules()) {
            if (!reached.test(rule.guard())) {
                continue;
            }
            Map<BindingId, Core> given = handedOver(answered, rule, answer);
            if (given == null) {
                continue;
            }
            for (StatedContract.Conjunct conjunct : rule.conjuncts()) {
                if (conjunct.stated() == null) {
                    continue;
                }
                Core here = Clauses.substituted(conjunct.stated(), given);
                out = predicates.assume(predicates.obligations(here, out, in.at(), false), out,
                        Known.Held.OF_THE_VALUE);
            }
        }
        return new Entered(out, in.at());
    }

    /**
     * What each name a rule reads stands for here: the parameters as this call handed them over, and
     * {@code value} as what the arm holds.
     *
     * <p>A rule is written in the declaration's names and read at the caller's values, so the two are
     * put together before anything is read of it — which is the same substitution a declaration's
     * clause gets where a value is built ({@link Clauses#statedAt}).
     *
     * <p>Null where the call and the declaration disagree about how many values were handed over.
     * That is a program this compiler is refusing elsewhere, and a rule read against the wrong
     * argument would be a relation nobody declared.
     */
    private static Map<BindingId, Core> handedOver(Answered answered,
                                                   StatedContract.StatedRule rule, Core answer) {
        List<Core> args = answered.call().args();
        if (args.size() != answered.stated().params().size()) {
            return null;
        }
        Map<BindingId, Core> given = new HashMap<>();
        for (BehaviorContract.ContractParam param : answered.stated().params()) {
            given.put(param.binding(), args.get(param.index()));
        }
        given.put(rule.value(), answer);
        return given;
    }

    /**
     * What an attempted construction's success branch is read under.
     *
     * <p>Reaching it is the construction having held, so the binding carries the type's invariant
     * exactly as an input of that type does — which is a location, and not the construction read
     * again. What the construction denotes is what a reading could say of the attempt, and an
     * attempt is written where it could not say enough: an expression it cannot name denotes
     * nothing, and inheriting that would drop the one thing reaching this branch established.
     *
     * <p>Its departures stand where the invariant did not hold and nothing was built, so none of
     * them is entered with anything the attempt would have guaranteed. That is the caller's to
     * honour by not asking.
     */
    Entered enteringBuilt(Core.IfConstructed ic, Known k, Denotations at) {
        return enter(Terms.read(ic.binder(), ic.construct().type(), ic.pos()), k, at);
    }

    // --- seeding -------------------------------------------------------------------------------

    /**
     * Seeds a reading with what the type of the value at {@code root} guarantees: a numeric
     * newtype's own invariant on its value, a predicate its invariant states of it, or a product
     * data's invariant over its fields (and one level of fields), each read at that very value.
     * Sound by closed construction — a value of type T was built through T's checked constructor.
     *
     * <p>Which is the same reading a construction gets, over field reads instead of field values: the
     * clause is the declaration's either way, and where it is established and where it is owed differ
     * only in direction.
     */
    Known seedAt(Core root, Known k, Denotations at, int depth) {
        return seedAt(root, FieldDomains.THE_VALUE, k, at, depth, FIELDS_SEEDED, new HashSet<>(),
                null, InvariantChecker.Reach.EVERYTHING);
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
     *
     * @param gathering told what this walk gathers, or null where nobody is collecting. A clause
     *                  governs a position from wherever it is written — the record the position is a
     *                  field of, and the declarations under that record it sits inside — and this
     *                  walk is where it is rebased onto the position it governs. A reader wanting
     *                  that list has to be told here or walk the same descent again and rebase it a
     *                  second way.
     */
    Known seedAt(Core root, String path, Known k, Denotations at, int depth, int limit,
                 Set<TypeSymbol> onPath, InvariantChecker.Gathering gathering,
                 InvariantChecker.Reach reach) {
        // Read before the path is entered, so that the one name and the other stay paired: a stop
        // taken after entering would leave the name on the path with nothing to take it off, and the
        // next field of the same type would be passed over as one already read. Supposed to hold
        // values, so nothing written under it is read: what is under it is what would say it holds
        // none, and reading it here is the supposing undone one step in.
        if (depth > limit || !(root.type() instanceof Type.Ref ref)
                || reach.stopAt().test(ref.name())) {
            return declining(root.type(), path, gathering, k);
        }
        if (!(symbols.declarations().declaration(ref.name().key()) instanceof Hir.Data data) || !onPath.add(ref.name())) {
            return declining(root.type(), path, gathering, k);
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
        Clauses.StatedClauses stated = reach.withoutClauses().test(ref.name())
                ? Clauses.StatedClauses.NONE_ASKED_FOR : clauses.statedAt(ref.name(), data, given);
        // A clause of a declaration under here that states nothing this can read is gone before any
        // reading sees it, and which position it was about goes with it. Said as it happens: a
        // reader collecting the clauses would otherwise take the ones it was handed for every
        // clause there is, and answer for a rule it never saw.
        if (gathering != null && !stated.everyClauseStated()) {
            gathering.missed(path);
        }
        for (Clauses.Stated one : stated.clauses()) {
            if (gathering != null) {
                gathering.gathered(ref.name(), one.expr());
            }
            predicates.quantifiedBy(one.expr(), at, true, quantified);
            out = predicates.assume(predicates.obligations(one.expr(), out, at, false), out,
                    Known.Held.OF_THE_VALUE);
        }
        out = out.and(quantified);
        if (data.newtype()) {
            // A newtype's `.value` is the same location as the newtype, so what its base guarantees is
            // guaranteed of this very atom: `data Outer = Inner` carries Inner's invariant.
            // A newtype's `.value` is at no path of its own, which is the rule `name` walks by:
            // wearing a name is not being somewhere else.
            Core value = given.get(bindings.get("value"));
            out = value == null ? declining(fields.get("value"), path, gathering, out)
                    : seedAt(value, path, out, at, depth + 1, limit, onPath, gathering, reach);
        } else {
            for (Map.Entry<String, BindingId> field : bindings.entrySet()) {
                Core value = given.get(field.getValue());
                if (value != null) {
                    out = seedAt(value, under(path, field.getKey()), out, at, depth + 1, limit,
                            onPath, gathering, reach);
                }
            }
        }
        onPath.remove(ref.name());
        return out;
    }

    /**
     * {@code k} as it stands, with the reading told where it is leaving rules unread.
     *
     * <p>Every way this walk stops short comes here: past the depth it reads to, at a value the
     * caller supposed holds values, at a type it has no declaration for, and at a name already on
     * the path. What a stop costs is not the same at each of them — most of them stop where there
     * was nothing to read — so what is asked is whether any rule stands under what is being left,
     * and only then is anything said. A walk that reported every stop would have a record with one
     * plain string field speaking for none of its positions.
     */
    private Known declining(Type type, String path, InvariantChecker.Gathering gathering, Known k) {
        if (gathering != null && type != null && anyRuleUnder(type, new HashSet<>())) {
            gathering.missed(path);
        }
        return k;
    }

    /**
     * Whether any rule is written anywhere under {@code type}.
     *
     * <p>A question about the model and not about the walk, which is what makes it the right one to
     * ask at a stop: the walk's own reach is what is being decided, so reading it would answer that
     * whatever was not read had nothing in it.
     *
     * <p>{@code seen} stops a type that holds its own kind. A name met on the way here was read
     * where it was met, so what it holds is accounted for and reaching it again adds nothing.
     */
    private boolean anyRuleUnder(Type type, Set<TypeSymbol> seen) {
        if (type instanceof Type.Ref ref) {
            if (!seen.add(ref.name())) {
                return false;
            }
            return switch (symbols.declarations().declaration(ref.name().key())) {
                // A unit data holds nothing and may write no rule about it (spec §unit-data), so a
                // sum of them is a type nothing is written under — which is what makes an
                // enumeration a position this still speaks for.
                case Hir.UnitData _ -> false;
                case Hir.SumData sum -> TypeOps.leafCases(sum, symbols).stream()
                        .anyMatch(each -> anyRuleUnder(Type.ref(each), seen));
                case Hir.Data data -> !clauses.declared(ref.name(), data).isEmpty()
                        || TypeOps.fieldTypes(data, symbols).values().stream()
                                .anyMatch(each -> anyRuleUnder(each, seen));
                case null, default -> false;
            };
        }
        boolean[] found = {false};
        Type.forEachChild(type, child -> found[0] |= anyRuleUnder(child, seen));
        return found[0];
    }

    /** A field of the value at {@code path}. The root of a newtype's own reading is the value it
     * wraps, which is at no path of its own, so its fields are the first step there is. */
    static String under(String path, String field) {
        return path.isEmpty() ? field : path + "." + field;
    }
}
