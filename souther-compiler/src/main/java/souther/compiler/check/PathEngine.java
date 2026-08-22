package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.check.BehaviorContract.Guard;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.Refinement;
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

    /**
     * Where a test in this package reads the answers this took a guarantee from, one entry per
     * seeding, and null everywhere else.
     *
     * <p>Beside {@link InvariantChecker#WATCHING} and for a reason of its own. Seeding one answer
     * twice lands on the subjects it landed on the first time, so a reading that seeds once per node
     * and one that seeds once per region say the same thing about every program — what separates
     * them is what they cost, and no diagnostic is about that. So the property has nowhere else to be
     * read, and one that nothing reads stops being true without anything failing.
     */
    static List<Core> SEEDED;

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

    PathEngine(Symbols symbols, Map<TypeSymbol, List<Hir.InvariantClause>> dischargeInvariants,
               ReadingPolicy policy) {
        this(symbols, dischargeInvariants, Map.of(), Terms.Of.THE_DISCHARGE_TREE, policy);
    }

    PathEngine(Symbols symbols, Map<TypeSymbol, List<Hir.InvariantClause>> dischargeInvariants,
               Map<ValueName.Behavior, StatedContract> contracts, ReadingPolicy policy) {
        this(symbols, dischargeInvariants, contracts, Terms.Of.THE_DISCHARGE_TREE, policy);
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
               Terms.Of reading, ReadingPolicy policy) {
        this(symbols, dischargeInvariants, Map.of(), reading, policy);
    }

    PathEngine(Symbols symbols, Map<TypeSymbol, List<Hir.InvariantClause>> dischargeInvariants,
               Map<ValueName.Behavior, StatedContract> contracts, Terms.Of reading,
               ReadingPolicy policy) {
        this.symbols = symbols;
        this.clauses = new Clauses(symbols, dischargeInvariants);
        this.terms = new Terms(symbols, reading, policy);
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
        Denotations next = at.location(root.binding(), terms.placeSubject(root.binding()),
                terms.placeTerm(root.binding()));
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
     * {@link Terms#affineOf} reads through it, and reads through a field taken off it the same way —
     * so there is no second reading for a fact about the name to be needed by. Recording one meant
     * giving the name's own atom the bounds of the form it was given, which is what a guard read one
     * way and a construction read the other had between them, and a bound is not a relation: it left
     * the guard settling nothing about the construction (#676).
     *
     * <p>What the binder means is {@link Terms#inside}'s answer and not this walk's. A reader that
     * decides for itself what a binder denotes is a second account of it, and the second account is
     * weaker than the first wherever it was written for a narrower purpose — which is what a
     * reduction's step read by (#867). Nothing else here is owed: the knowledge is what stood before
     * the binding, because the initializer was read before this.
     */
    Entered bindLet(Core.LetIn li, Known k, Denotations at) {
        return new Entered(k, terms.inside(li, at));
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
     * named — the case's value names only itself. What the arm binds is a place, which is what lets
     * a clause be read against it and what makes it carry what its type guarantees. Which value it
     * is is a second answer and comes from what was opened ({@link #opening}).
     *
     * <p>An arm that binds nothing introduces nothing, and its body is read as the arm's own. Held
     * here rather than at each walk: two readings deciding it apart is two chances to forget, and
     * the one that forgot fell over on every ordinary unit case.
     */
    Entered enteringArm(Core.Case arm, Core scrutinee, Known k, Denotations at) {
        Entered in = arm.binder() == null || arm.bindType() == null
                ? new Entered(k, at)
                : opening(arm, scrutinee, k, at);
        return whatTakingThisCaseSays(arm, scrutinee,
                assuming(answeredBy(scrutinee, in.at()), answered(arm, scrutinee),
                        guard -> impliedBy(guard, arm.pattern()), in));
    }

    /**
     * {@code in} with what taking this arm's case says about what the operation was given.
     *
     * <p>An operation answering its number as one case of a union answers none under a condition it
     * declares ({@link DischargeRules.AnsweredUnless}), and which arm was taken settles that
     * condition both ways: the arm carrying the number was taken because it does not hold, and any
     * other arm because it does. So a {@code DivisionByZero} arm has established that the divisor is
     * zero, which is a fact about a value the caller handed over and not about the case.
     *
     * <p>Taken in through the door a written condition goes through, which is what keeps this one
     * statement rather than two: what a comparison establishes is {@link Predicates}' to say, and a
     * reader that asserted the relation itself would be a second account of what {@code == 0} means.
     *
     * <p>An arm naming several cases says neither thing where the number's case is among them: it
     * may have been taken for that one or for another, and a rule about a value this arm may not
     * have is a rule about nothing.
     */
    private Entered whatTakingThisCaseSays(Core.Case arm, Core scrutinee, Entered in) {
        Core called = originating(scrutinee, in.at(), new HashSet<>());
        DischargeRules.NumericResult result = called == null ? null
                : DischargeRules.numericResult(Terms.operationOf(called));
        if (result == null || result.unless() == null
                || !(result.at() instanceof DischargeRules.Answered.InTheCaseCarrying(
                        Type answersIn))) {
            return in;
        }
        Boolean answered = whetherItAnswered(arm, answersIn);
        if (answered == null) {
            return in;
        }
        Core args = Terms.argsOf(called)
                .get(result.unless().argument().positionIn(Terms.operationOf(called)));
        Core condition = new Core.Binary(result.unless().op(), args,
                numberOf(result.unless().than(), args.type(), args.pos()),
                souther.compiler.types.CoverageOrigin.unwritten(), Type.BOOL, args.pos());
        return new Entered(assuming(condition, in.known(), in.at(), !answered).known(), in.at());
    }

    /** Whether {@code arm} was taken because the operation answered its number, or because it did
     * not — and null where the arm says neither. */
    private static Boolean whetherItAnswered(Core.Case arm, Type answersIn) {
        boolean itsCase = false;
        boolean another = false;
        for (CaseSelector selector : arm.pattern().selectors()) {
            if (answersIn.equals(selector.refinement().bound())) {
                itsCase = true;
            } else {
                another = true;
            }
        }
        return itsCase == another ? null : itsCase;
    }

    /** {@code n} written at the type the argument is, so that the condition compares two values of
     * one type as a source-written one would. */
    private static Core numberOf(long n, Type type, souther.compiler.diag.SourcePos pos) {
        return type == Type.DECIMAL
                ? new Core.Decimal(java.math.BigDecimal.valueOf(n), type, pos)
                : new Core.Int(n, type, pos);
    }

    /**
     * The arm's binding entered as the value it opens.
     *
     * <p>An arm that names one case of a declared sum, and one that names several, bind the value
     * they were given — the case's own class is what is tested and the value read is that instance
     * ({@link Refinement.Direct}). So the arm is not introducing a value; it is saying which case the
     * one already there is, and what it binds is about that same value. Entered as a place all the
     * same, because a place is what a clause may be read against and what the seeding writes about,
     * and which value it is and what may be done with it are two answers.
     *
     * <p>Introduced afresh where the two are really different values. An optional's present carrier
     * binds what stands under it, which is not the optional.
     *
     * <p>Held one way and not two: an arm that made a second subject for the value it opened had
     * every fact about the answer filed under one and every fact the arm added under the other, and
     * the two agreed only for as long as nothing could tell them apart (#824).
     */
    private Entered opening(Core.Case arm, Core scrutinee, Known k, Denotations at) {
        Core.Read root = Terms.read(arm.binder(), arm.bindType(), arm.pos());
        Opens opens = opens(arm, scrutinee, at);
        Denotations next = opens == null
                ? at.location(root.binding(), terms.placeSubject(root.binding()),
                        terms.placeTerm(root.binding()))
                : at.opened(root.binding(), opens.value(), opens.subject(),
                        opens.term() != null ? opens.term() : terms.placeTerm(root.binding()),
                        opens.numeric());
        return new Entered(seedAt(root, k, next, 0), next);
    }

    /**
     * What an arm's binding stands for: the value the walk reached where the two are one value, the
     * subject facts about it are filed under, what the term grammar names it by where the arithmetic
     * it opened names it, and which arithmetic that is.
     *
     * <p>Taken together because they are one answer about one binding, and handing them over apart is
     * how one of them was left behind. Four answers and not one: the value is where it came from,
     * which is how a rule declared about an answer is found through however many names the answer
     * went by, and the arithmetic is what was computed to make it. An arm opening the number a
     * library operation answered as a case is where the two are furthest apart — the value it stands
     * for is the union, and the number it is is a quotient of two operands the union does not carry.
     */
    private record Opens(Core value, FactSubject subject, Term term, NumericMeaning numeric) {}

    /**
     * What the arm's binding opens, or null where nothing here says.
     *
     * <p>Asked of what the pattern binds and not of what the arm looks like. A case whose carrier is
     * the value binds that value, so the binding stands for the scrutinee and is about it. An
     * optional's present carrier binds what stands under it: a different value, named as what that
     * optional holds, and one no expression here is — so it is about something while standing for
     * nothing. An absent carrier binds nothing at all. That is the whole of it — {@link Refinement}
     * has three answers and each one settles this.
     */
    private Opens opens(Core.Case arm, Core scrutinee, Denotations at) {
        FactSubject of = terms.subjectOf(scrutinee, at);
        if (of == null) {
            return null;
        }
        return switch (arm.pattern().binding()) {
            case Refinement.Direct(Type carried) -> arithmetic(carried, scrutinee, at);
            case Refinement.OptionPresent ignored -> new Opens(null, terms.heldBy(of), null, null);
            case Refinement.OptionAbsent ignored -> null;
        };
    }

    /**
     * The arm's binding as the number a library operation computed, where the case it opened is
     * where that operation answers one — and as the value the walk reached otherwise.
     *
     * <p>Which case was opened is decided here and the arithmetic is not. What an operation computes
     * and where it answers it is one row of one table (spec §invariant-discharge-arithmetic), and
     * this reads the row: a reader that recognised {@code divide} for itself would be a second place
     * deciding which spellings are divisions, and the next operation answering a number as a case
     * would be a third.
     *
     * <p>Read through the names the call was given, as everything else about a scrutinee is: {@code
     * let q = Int.divide(a, b)} and a {@code match} written straight over the call are the same
     * program, and a binding between the two is a name for the call rather than a step away from it.
     */
    private Opens arithmetic(Type carried, Core scrutinee, Denotations at) {
        Core called = originating(scrutinee, at, new HashSet<>());
        DischargeRules.NumericResult result = called == null ? null
                : DischargeRules.numericResult(Terms.operationOf(called));
        if (result == null || !(result.at() instanceof DischargeRules.Answered.InTheCaseCarrying(
                Type answersIn)) || !answersIn.equals(carried)) {
            return new Opens(scrutinee, terms.subjectOf(scrutinee, at), null, null);
        }
        NumericMeaning meaning = result.computes().of(Terms.argsOf(called));
        FactSubject subject = terms.subjectOpenedAs(meaning, carried, called, at);
        // A call the term grammar cannot name leaves the number it answers named by nothing this can
        // relate to anything else, and a binding standing for the value it opened is what an arm has
        // always given. Nothing is lost by declining here; what is lost by naming it anyway is the
        // one thing an atom asserts, which is that two writings of it are one value.
        return subject == null ? new Opens(scrutinee, terms.subjectOf(scrutinee, at), null, null)
                : new Opens(scrutinee, subject,
                        terms.termOpenedAs(meaning, carried, called, at), meaning);
    }

    /** The call {@code value} came from, through however many names it was given, or null where it
     * came from something else. As {@link #originatingCall}, of a call in either representation:
     * what an operation computes is a question about the operation, not about which tree is being
     * read. */
    private Core originating(Core value, Denotations at, Set<BindingId> seen) {
        if (Terms.operationOf(value) != null) {
            return value;
        }
        if (value instanceof Core.Read read && seen.add(read.binding())) {
            Core given = at.valueOf(read.binding());
            return given == null || given == value ? null : originating(given, at, seen);
        }
        return null;
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
        return arm.binder() == null || arm.bindType() == null ? scrutinee
                : Terms.read(arm.binder(), arm.bindType(), arm.pos());
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
                if (conjunct.stated().orNull() == null) {
                    continue;
                }
                Core here = Clauses.substituted(conjunct.stated().orNull(), given);
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
     * {@code k} with what every answer read here guarantees taken as holding of it: what its type
     * states of any value of that type, and what its behavior declared of every answer it gives.
     *
     * <p>An answer is a value of its type, built through that type's checked constructor — the same
     * argument {@link #enter} rests on for a parameter, for what a {@code match} arm binds, and for
     * what a combinator hands its closure. It was not asked of an answer only because an answer had
     * nothing to be asked about: no subject, so nothing to write the guarantee under. It has one now.
     *
     * <p>What makes an answer one of these is not the shape of the node. It is that whoever produced
     * it had already established what its type states before handing it over — a boundary this check
     * read on its own, or one another compile read and published. A call to a behavior is that today,
     * and if another way of invoking one turns out to carry the same guarantee it belongs here too. A
     * construction written here is not: it is the very thing being judged, and seeding it assumes
     * what the judgement is about. Written that way first, a construction over a value nothing was
     * known of came out proved — and came out proved with the clause meant to establish it taken
     * away, which is the shape of a check that has stopped checking.
     *
     * <p>Only what holds of every answer. A rule under a case is about an answer that is that case,
     * and nothing here has opened one; that rule is taken in where the case is known, which is at the
     * arm ({@link #enteringArm}). A rule under no case holds of whatever the behavior answered, so
     * the call is where it is known.
     *
     * <p>Sound for a behavior that reaches outside the language, and for the same reason it is sound
     * for one that does not. Two writings of such a call are two evaluations and so two subjects, but
     * each invocation answers something its own declaration holds of it. What the effect decides is
     * whether the two may be identified, not whether either of them was declared about.
     *
     * <p>Held of the value and not of the path. What is guaranteed of a value is true wherever that
     * value is named, and an evaluation is named at one place, so there is no branch on which it is
     * less true.
     *
     * <p>Read over the expression rather than at each call's own step in the walk, because a
     * construction is judged when the walk reaches it and the answers it is built from stand
     * underneath it.
     *
     * <p>As far as the expression is <em>reached</em>, and no further. Standing in the subtree is not
     * standing where the walk is: a branch is read under the condition that chose it, and a call in
     * the arm beside it is one this path never evaluates. Taken in from there, what that call
     * guarantees is a fact about a value that was never produced — and since a guarantee constrains
     * the arguments it relates the answer to, it lands on the very values the condition is about. One
     * arm's answer then contradicts the other arm's condition, the reading comes out reaching
     * nothing, and the arm is walked no further: its constructions are not judged and nothing is
     * said. So this stops where the walk branches, and each branch's own reading seeds what stands in
     * it. Blocks stop it too — what a closure's body answers is decided where the closure is applied,
     * and what a binding inside one holds is not settled from out here.
     */
    Known answering(Core e, Known k, Denotations at) {
        if (e instanceof Core.Block) {
            return k;
        }
        Known out = k;
        if (isACheckedProducer(e)) {
            seeded(e);
            out = seedAt(e, out, at, 0);
        }
        out = assuming(answeredBy(e, at), e, guard -> guard instanceof Guard.Always,
                new Entered(out, at)).known();
        // Only what is evaluated by reaching here. What each branch holds is that branch's to read.
        return switch (e) {
            case Core.If x -> answering(x.cond(), out, at);
            case Core.Match x -> answering(x.scrutinee(), out, at);
            case Core.IfConstructed x -> answering(x.construct(), out, at);
            // A binding's body is read once the binding is entered, and not from out here: what its
            // initializer denotes is not settled until `bindLet` has run, so an answer read through a
            // name from here would be given a subject the name does not have yet.
            case Core.LetIn x -> answering(x.value(), out, at);
            default -> {
                Known[] threaded = {out};
                Core.forEachChild(e, child -> threaded[0] = answering(child, threaded[0], at));
                yield threaded[0];
            }
        };
    }

    /** Records an answer this read a guarantee off, where a test is reading them. */
    private static void seeded(Core answer) {
        List<Core> watching = SEEDED;
        if (watching != null) {
            watching.add(answer);
        }
    }

    /**
     * Whether reaching {@code e} means reaching a value whose type's invariant something already
     * established.
     *
     * <p>Asked of what produced the value, and of nothing else. Not of the subject it was given: what
     * kind of subject a value has says whether two writings of it may be identified, which is a
     * different question with a different answer, and reading one as the other would take the
     * guarantee away from any answer that turned out to be shareable. Not of whether a contract was
     * declared either — that is what an {@code ensures} is, and a behavior with none still answers a
     * value of its type.
     *
     * <p>A call to a behavior is one: its implementation is a body this check read, or one another
     * compile read and published, and either way the construction was checked there. A construction
     * written here is not — it is the very thing being judged.
     */
    private boolean isACheckedProducer(Core e) {
        return e instanceof Core.Call call && call.fn() instanceof Core.Reached reached
                && reached.denotes() instanceof ValueName.Behavior;
    }

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
        // Asked one at a time, because a stop says two things and only one of them is the same for
        // all of these: whether the rules under it were read, and whether a construction could have
        // got out of making the value they are about.
        if (depth > limit) {
            // A limit on how far a measurement is worth carrying, which is not a limit on the model:
            // a rule four records down refuses the outermost construction exactly as one on its own
            // fields does.
            return declining(root.type(), path, gathering, k,
                    InvariantChecker.Borne.BY_EVERY_VALUE);
        }
        if (!(root.type() instanceof Type.Ref ref)) {
            // Not a declaration of its own: a container or an optional, whose element is a value
            // that need not be there, or a type nothing is written under at all.
            return declining(root.type(), path, gathering, k,
                    InvariantChecker.Borne.BY_SOME_VALUES);
        }
        if (reach.stopAt().test(ref.name())) {
            // Left out because this reading was asked to leave it out, which is still a rule of a
            // value every construction has to make.
            return declining(root.type(), path, gathering, k,
                    InvariantChecker.Borne.BY_EVERY_VALUE);
        }
        if (!(symbols.declarations().declaration(ref.name().key()) instanceof Hir.Data data)) {
            // A choice between declarations, which is the only kind that reaches here holding a rule
            // at all: a unit holds none and a name standing for nothing declares none. A
            // construction picks one of the cases, so a rule written on one of them refuses values
            // of that case and not every value of this.
            return declining(root.type(), path, gathering, k,
                    InvariantChecker.Borne.BY_SOME_VALUES);
        }
        if (!onPath.add(ref.name())) {
            // Already met on the way down, so entering it again reads the rules that were read where
            // it was met. A record holding one of its own kind stops here and nothing is short of
            // anything for it.
            return declining(root.type(), path, gathering, k,
                    InvariantChecker.Borne.BY_SOME_VALUES);
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
            gathering.missed(path, InvariantChecker.Borne.BY_EVERY_VALUE);
        }
        for (Clauses.Stated one : stated.clauses()) {
            // Where this clause becomes a rule of the model something can be attributed to. What is
            // read off it below belongs to this rule, and the identity is settled here so that no
            // reader of the reading has to decide which of the rules of the model it is holding.
            RuleRef.Invariant origin = new RuleRef.Invariant(one.clause().ref());
            // Read before it is handed over, so that what is recorded is this reading's own answer
            // about this clause rather than a guess made from its shape somewhere else.
            Predicates.Owed owed = gathering == null
                    ? predicates.obligations(one.expr(), out, at, false)
                    : predicates.obligations(one.expr(), out, at, false,
                            (part, said) -> gathering.constrained(origin, part,
                                    InvariantChecker.partRead(said)));
            if (gathering != null) {
                gathering.gathered(origin, one.expr(), Predicates.subjectsIn(owed));
            }
            predicates.quantifiedBy(one.expr(), at, true, quantified);
            out = predicates.assume(owed, out, Known.Held.OF_THE_VALUE);
        }
        out = out.and(quantified);
        if (data.newtype()) {
            // A newtype's `.value` is the same location as the newtype, so what its base guarantees is
            // guaranteed of this very atom: `data Outer = Inner` carries Inner's invariant.
            // A newtype's `.value` is at no path of its own, which is the rule `name` walks by:
            // wearing a name is not being somewhere else.
            Core value = given.get(bindings.get("value"));
            out = value == null
                    ? declining(fields.get("value"), path, gathering, out,
                            InvariantChecker.Borne.BY_EVERY_VALUE)
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
    private Known declining(Type type, String path, InvariantChecker.Gathering gathering, Known k,
                            InvariantChecker.Borne borne) {
        if (gathering != null && type != null && anyRuleUnder(type, new HashSet<>())) {
            gathering.missed(path, borne);
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
