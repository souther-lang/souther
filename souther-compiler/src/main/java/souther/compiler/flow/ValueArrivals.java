package souther.compiler.flow;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The ways an expression arrives at a value, read off the body it is written in.
 *
 * <p>One reading for three questions that were being answered separately and had to agree: whether
 * an expression can be evaluated to a value at all, what that value is where it is a truth, and
 * under what conditions each way there holds. The first two are read off the body and are the same
 * whoever is asking; the third is written in whatever words the {@link Naming} has, and a naming
 * with no words for a condition leaves the path {@link Completeness#PARTIAL} rather than leaving the
 * arrival out. So what the numbering can place decides how a way is written down and never whether
 * there is one.
 *
 * <p><b>Rooted at a body.</b> What a name reads is not a fact about the node that reads it: the same
 * {@code Core.Read} is a position of the input in one body and a {@code let} away from a number
 * written out in another. So the body is read once, every occurrence in it is settled under what the
 * binders above it bound, and a caller asks about a node it already has. A node this was not rooted
 * at is read as its own body, which is the honest answer for one — every name in it is free, because
 * nothing here bound them.
 *
 * <p><b>An arrival is a value.</b> Two that say the same thing are one way. The answers are sets for
 * that reason and not as an optimisation: a way found twice by a reading that got there two ways is
 * still one way in, and anything counting these is counting what the body does.
 */
public final class ValueArrivals<P> {

    private final Naming<P> naming;

    /**
     * What each occurrence was settled as, keyed by identity.
     *
     * <p>Sound because a node occurs once, and what is in scope at it is what the reading had when
     * it got there — so the environment is a function of the position and not a second key.
     */
    private final IdentityHashMap<Core, Set<Arrival<P>>> settled = new IdentityHashMap<>();

    private ValueArrivals(Naming<P> naming) {
        this.naming = naming;
    }

    /** The reading of {@code body}, with every occurrence in it settled under what binds it. */
    public static <P> ValueArrivals<P> ofBody(Core body, Naming<P> naming) {
        ValueArrivals<P> reading = new ValueArrivals<>(naming);
        if (body != null) {
            reading.fill(body, naming, Map.of());
        }
        return reading;
    }

    /** Whether {@code e} can be evaluated to a value. */
    public static boolean arrives(Core body, Core e) {
        return ofBody(body, Anonymous.NAMING).arrivesAt(e);
    }

    /** The ways {@code e} arrives at a value, empty where no run arrives at one. */
    public Set<Arrival<P>> at(Core e) {
        if (e == null) {
            return Set.of();
        }
        Set<Arrival<P>> already = settled.get(e);
        if (already != null) {
            return already;
        }
        // Not rooted here, so read as its own body: nothing above it bound anything.
        fill(e, naming, Map.of());
        return settled.getOrDefault(e, Set.of());
    }

    /** Whether {@code e} can be evaluated to a value. */
    public boolean arrivesAt(Core e) {
        return !at(e).isEmpty();
    }

    /**
     * Whether {@code e} can come out {@code want}.
     *
     * <p>Read off what the arrivals come to and nothing else, so it is the same answer whichever
     * naming is asking. A way whose value is unread may be either, so it answers for both — which is
     * this reading having nothing to say and not this reading saying both.
     */
    public boolean comesOut(Core e, boolean want) {
        return comesOut(at(e), want);
    }

    /** The same, of arrivals already in hand. */
    private static <P> boolean comesOut(Set<Arrival<P>> arrivals, boolean want) {
        for (Arrival<P> each : arrivals) {
            if (each.value() == Truth.UNREAD || each.value() == Truth.of(want)) {
                return true;
            }
        }
        return false;
    }

    /**
     * The ways {@code e} is settled to {@code want}, or that this reading cannot enumerate them.
     *
     * <p>All of them or none. One arrival whose value is unread may be among the ways to either
     * truth, and one whose path the naming could not write down whole is a way nothing can be
     * steered along — either way no list of them is complete, and an incomplete list is worse here
     * than no list because whatever takes one reads the ways it does not hold as ways the body has
     * not got.
     */
    public Ways<P> waysTo(Core e, boolean want) {
        return waysTo(at(e), want);
    }

    /** The same, of arrivals already in hand. */
    private static <P> Ways<P> waysTo(Set<Arrival<P>> arrivals, boolean want) {
        List<P> paths = new ArrayList<>();
        for (Arrival<P> each : arrivals) {
            if (each.value() == Truth.UNREAD || !each.isComplete()) {
                return new Ways.Unknown<>();
            }
            if (each.value() == Truth.of(want)) {
                paths.add(each.path());
            }
        }
        return new Ways.Known<>(paths);
    }

    // ---------------------------------------------------------------- filling

    /**
     * Settle {@code e} and everything written inside it, each under what binds it.
     *
     * <p>Into the parts as they are written and not as they are evaluated. A {@code Block} is a
     * function value and what it comes to is not read through, but its body is written here and a
     * caller may ask about a node in it — so it is settled too, under its own parameters, and the
     * answer for the block itself stays what it is.
     */
    private void fill(Core e, Naming<P> naming, Map<BindingId, Bound<P>> bound) {
        if (e == null || settled.containsKey(e)) {
            return;
        }
        read(e, naming, bound);
        switch (e) {
            case Core.LetIn let -> {
                fill(let.value(), naming, bound);
                fill(let.body(), naming.under(let.binder(), let.value()),
                        with(bound, let.binder(), read(let.value(), naming, bound), let.value()));
            }
            case Core.Block block -> {
                Map<BindingId, Bound<P>> inner = bound;
                for (Hir.Binder param : block.params()) {
                    inner = with(inner, param, oneWay(), null);
                }
                fill(block.body(), naming, inner);
            }
            case Core.Match match -> {
                fill(match.scrutinee(), naming, bound);
                for (Core.Case arm : match.cases()) {
                    fill(arm.body(), naming, with(bound, arm.binding(), oneWay(), null));
                }
            }
            case Core.IfConstructed constructed -> {
                constructed.construct().values()
                        .forEach(given -> fill(given.value(), naming, bound));
                fill(constructed.then(), naming, with(bound, constructed.binder(), oneWay(), null));
                constructed.els().forEach(arm -> fill(arm.body(), naming, bound));
            }
            default -> {
                for (Core child : partsOf(e)) {
                    fill(child, naming, bound);
                }
            }
        }
    }

    /**
     * {@code bound} widened by one binder, or itself where the binder is not there.
     *
     * <p>Two things about the name and not one. What it was settled to is what a reading of its value
     * takes; what it was written as is what a reading asking which position it is about takes, and a
     * name bound to nothing this can read — a parameter, an arm's binding — is a position in its own
     * right rather than a name with no answer.
     */
    private Map<BindingId, Bound<P>> with(Map<BindingId, Bound<P>> bound, Hir.Binder binder,
                                          Set<Arrival<P>> arrivals, Core settledBy) {
        if (binder == null) {
            return bound;
        }
        Map<BindingId, Bound<P>> inner = new java.util.HashMap<>(bound);
        inner.put(binder.binding(), new Bound<>(arrivals, settledBy));
        return Map.copyOf(inner);
    }

    /**
     * What a name in scope stands for: the ways its value arrives, and the expression it was settled
     * to where the body settled it to one.
     *
     * @param settledBy null for a name nothing here bound a value to, which is a position of whatever
     *                  the body is handed
     */
    private record Bound<P>(Set<Arrival<P>> arrivals, Core settledBy) { }

    // ---------------------------------------------------------------- reading

    private Set<Arrival<P>> read(Core e, Naming<P> naming, Map<BindingId, Bound<P>> bound) {
        if (e == null) {
            // A body the checker refused a clause of arrives with a hole where the clause was.
            // Nothing is evaluated there and nothing arrives.
            return Set.of();
        }
        Set<Arrival<P>> already = settled.get(e);
        if (already != null) {
            return already;
        }
        Refusals refused = new Refusals();
        Set<Arrival<P>> answer = reading(e, naming, bound, refused);
        if (answer.isEmpty() && refused.any) {
            // No arrival is not a proof that no value arrives, and this is not the reading that
            // could give one. Where every way out of here settles a decision the way in settled the
            // other way, what is missing is this reading following a correlation and not the body
            // having a path. So it is answered as one this has nothing to say about.
            answer = oneWay();
        }
        settled.put(e, answer);
        return answer;
    }

    private Set<Arrival<P>> reading(Core e, Naming<P> naming, Map<BindingId, Bound<P>> bound,
                                    Refusals refused) {
        return switch (e) {
            case Core.Unreachable ignored -> Set.of();
            case Core.Bool literal -> one(Truth.of(literal.value()), whole(naming.nowhere()));
            case Core.Read read -> {
                Bound<P> named = bound.get(read.binding());
                yield named != null ? named.arrivals() : oneWay();
            }
            // A function value, not a body being run here. What happens when a call applies it is
            // that call's business, and a call is not read through either.
            case Core.Block ignored -> oneWay();
            // The value is evaluated before the body it binds is.
            case Core.LetIn let -> {
                Set<Arrival<P>> value = read(let.value(), naming, bound);
                yield value.isEmpty() ? Set.of()
                        : read(let.body(), naming.under(let.binder(), let.value()),
                                with(bound, let.binder(), value, let.value()));
            }
            case Core.Binary binary when shortCircuits(binary.op()) ->
                    through(binary, naming, bound, refused);
            case Core.If iff -> fork(iff, naming, bound, refused);
            case Core.Match match -> arms(match, naming, bound, refused);
            case Core.IfConstructed constructed -> attempted(constructed, naming, bound, refused);
            case Core.PreservedCall preserved -> throw preserved.unexpectedIn("value-flow analysis");
            default -> built(e, naming, bound, refused);
        };
    }

    /**
     * A value made out of several, settled every way its parts are settled together.
     *
     * <p>One rule and not a case each: what it does not cover is exactly what forks, what stops
     * early, what names, and what comes out one of two ways against another value. A part that
     * arrives at no value leaves the whole arriving at none, which is what makes this the reading of
     * everything strict as well.
     */
    private Set<Arrival<P>> built(Core e, Naming<P> naming, Map<BindingId, Bound<P>> bound,
                                  Refusals refused) {
        Set<Arrival<P>> out = oneWay();
        for (Core part : partsOf(e)) {
            Set<Arrival<P>> each = read(part, naming, bound);
            if (each.isEmpty()) {
                return Set.of();
            }
            out = product(out, each, naming, refused);
            if (out.size() > naming.mostArrivals()) {
                return oneWay();
            }
        }
        if (e instanceof Core.Binary comparison && compares(comparison.op()) && out.size() == 1) {
            Set<Arrival<P>> settledTwoWays = comparedOut(comparison, out.iterator().next(), naming,
                    read -> {
                        Bound<P> named = bound.get(read.binding());
                        return named == null ? null : named.settledBy();
                    });
            if (settledTwoWays != null) {
                return settledTwoWays;
            }
        }
        return out;
    }

    /**
     * A comparison split into the ways it comes out, or null where none of them is witnessed.
     *
     * <p>Asked one way at a time. There is no rule here that a comparison comes out both ways: each
     * way is answered for on its own, by whether a value of what is compared brings it out that way,
     * and a way nothing stands behind is not among these. That is what keeps {@code 1 > 2} and
     * {@code a == a} from being read as values that vary.
     *
     * <p>Asked where nothing under the comparison was already saying the value varies, so what is
     * read here is added to the reading and nothing is taken out of it.
     */
    private Set<Arrival<P>> comparedOut(Core.Binary comparison, Arrival<P> under, Naming<P> naming,
                                        java.util.function.Function<Core.Read, Core> settledBy) {
        boolean holds = Witnessed.comesOut(comparison, true, settledBy);
        boolean fails = Witnessed.comesOut(comparison, false, settledBy);
        if (!holds && !fails) {
            return null;
        }
        Set<Arrival<P>> out = new LinkedHashSet<>();
        if (holds) {
            side(comparison, true, under, naming, out);
        }
        if (fails) {
            side(comparison, false, under, naming, out);
        }
        return out.isEmpty() ? null : out;
    }

    private void side(Core.Binary comparison, boolean held, Arrival<P> under, Naming<P> naming,
                      Set<Arrival<P>> out) {
        P named = naming.side(comparison, held);
        if (named == null) {
            // The way is there and this naming has no words for it.
            out.add(new Arrival<>(Truth.of(held), under.provenance().partial()));
            return;
        }
        P both = naming.join(under.path(), named);
        if (both == null) {
            return;
        }
        out.add(new Arrival<>(Truth.of(held),
                new Provenance<>(both, under.provenance().completeness())));
    }

    /**
     * The ways to the value of an operator that stops as soon as its answer is settled.
     *
     * <p>Not a product of the two sides. {@code &&} comes to false wherever the left does and never
     * looks at the right, and comes to whatever the right does wherever the left went through — so
     * the ways are the left's settling ones as they stand, and the left's going-through ones each
     * extended by every way of the right.
     *
     * <p>A left way this reading cannot value is not one of either. Whether the right ran at all is
     * what the left's value would have said, so the way arrives where the right does and nowhere
     * this reading can point at otherwise: where the right arrives at no value, claiming this way
     * arrives would be reading "I cannot say which" as "it comes out the way that stops here".
     */
    private Set<Arrival<P>> through(Core.Binary binary, Naming<P> naming,
                                    Map<BindingId, Bound<P>> bound, Refusals refused) {
        Truth goesOn = binary.op() == Hir.BinOp.AND ? Truth.TRUE : Truth.FALSE;
        Set<Arrival<P>> left = read(binary.left(), naming, bound);
        Set<Arrival<P>> right = read(binary.right(), naming, bound);
        Set<Arrival<P>> out = new LinkedHashSet<>();
        for (Arrival<P> each : left) {
            if (each.value() == goesOn) {
                under(each.provenance(), right, naming, out, refused);
            } else if (each.value() == Truth.UNREAD) {
                if (!right.isEmpty()) {
                    out.add(each);
                }
            } else {
                out.add(each);
            }
            if (out.size() > naming.mostArrivals()) {
                return oneWay();
            }
        }
        return out;
    }

    private Set<Arrival<P>> fork(Core.If iff, Naming<P> naming,
                                 Map<BindingId, Bound<P>> bound, Refusals refused) {
        // Numbered where they are written and not where they survive: the arm a fork answers on is
        // its place among the arms, and one that answers nothing is skipped rather than closing the
        // gap and letting the next arm be called the first.
        Core[] arms = {iff.then(), iff.els()};
        Set<Arrival<P>> cond = read(iff.cond(), naming, bound);
        Set<Arrival<P>> out = new LinkedHashSet<>();
        for (int part = 0; part < arms.length; part++) {
            boolean want = part == 0;
            if (!comesOut(cond, want)) {
                continue;
            }
            Set<Arrival<P>> body = read(arms[part], naming, bound);
            if (body.isEmpty()) {
                continue;
            }
            for (Provenance<P> way : waysIn(cond, iff, part, want, naming)) {
                under(way, body, naming, out, refused);
            }
            if (out.size() > naming.mostArrivals()) {
                return oneWay();
            }
        }
        return out;
    }

    /**
     * The ways into arm {@code part}, as the condition's ways of coming out that way where they can
     * all be written down, and as the arm itself where they cannot.
     *
     * <p>Which arms there are is settled before this, off what the condition comes out as. This
     * settles only how a way into one is written, so a naming with no words for the fork leaves the
     * way {@link Completeness#PARTIAL} and takes no arm away.
     */
    private List<Provenance<P>> waysIn(Set<Arrival<P>> cond, Core.If iff, int part, boolean want,
                                       Naming<P> naming) {
        if (waysTo(cond, want) instanceof Ways.Known<P> known && !known.paths().isEmpty()) {
            return known.paths().stream().map(this::whole).toList();
        }
        return List.of(armWay(iff, part, naming));
    }

    /** The arm itself as the one way in, for a condition whose ways cannot all be written down. */
    private Provenance<P> armWay(Core fork, int part, Naming<P> naming) {
        P named = naming.forkArm(fork, part);
        return named == null
                ? new Provenance<>(naming.nowhere(), Completeness.PARTIAL) : whole(named);
    }

    private Set<Arrival<P>> arms(Core.Match match, Naming<P> naming,
                                 Map<BindingId, Bound<P>> bound, Refusals refused) {
        if (read(match.scrutinee(), naming, bound).isEmpty()) {
            return Set.of();
        }
        Set<Arrival<P>> out = new LinkedHashSet<>();
        for (int part = 0; part < match.cases().size(); part++) {
            Core.Case arm = match.cases().get(part);
            Set<Arrival<P>> body = read(arm.body(), naming, with(bound, arm.binding(), oneWay(), null));
            if (body.isEmpty()) {
                continue;
            }
            P named = naming.matchCase(match, part);
            Provenance<P> way = named == null
                    ? new Provenance<>(naming.nowhere(), Completeness.PARTIAL) : whole(named);
            under(way, body, naming, out, refused);
            if (out.size() > naming.mostArrivals()) {
                return oneWay();
            }
        }
        return out;
    }

    private Set<Arrival<P>> attempted(Core.IfConstructed constructed, Naming<P> naming,
                                      Map<BindingId, Bound<P>> bound, Refusals refused) {
        for (Core.FieldValue given : constructed.construct().values()) {
            if (read(given.value(), naming, bound).isEmpty()) {
                return Set.of();
            }
        }
        List<Core> arms = new ArrayList<>();
        arms.add(constructed.then());
        constructed.els().forEach(arm -> arms.add(arm.body()));
        Set<Arrival<P>> out = new LinkedHashSet<>();
        for (int part = 0; part < arms.size(); part++) {
            Map<BindingId, Bound<P>> inner =
                    part == 0 ? with(bound, constructed.binder(), oneWay(), null) : bound;
            Set<Arrival<P>> body = read(arms.get(part), naming, inner);
            if (body.isEmpty()) {
                continue;
            }
            under(armWay(constructed, part, naming), body, naming, out, refused);
            if (out.size() > naming.mostArrivals()) {
                return oneWay();
            }
        }
        return out;
    }

    // ------------------------------------------------------------ putting ways together

    /** Each arrival held to what already holds along the way to it, into {@code out}. */
    private void under(Provenance<P> holds, Set<Arrival<P>> arrivals, Naming<P> naming,
                       Set<Arrival<P>> out, Refusals refused) {
        for (Arrival<P> each : arrivals) {
            P both = naming.join(holds.path(), each.path());
            if (both == null) {
                refused.any = true;
                continue;
            }
            out.add(new Arrival<>(each.value(), new Provenance<>(both,
                    holds.completeness().and(each.provenance().completeness()))));
        }
    }

    /**
     * Every way the two can be settled together, which is not every pairing of them.
     *
     * <p>A binding read twice is one decision read twice, and pairing its ways without asking
     * whether the two agree would report a value settled nine ways that is settled three.
     *
     * <p>What the parts of a value come to is not what the value comes to. A thing built out of
     * several is the constructor's answer and no way to it carries a truth of its own, so these
     * arrive with nothing said about which of the two they are.
     */
    private Set<Arrival<P>> product(Set<Arrival<P>> left, Set<Arrival<P>> right, Naming<P> naming,
                                    Refusals refused) {
        Set<Arrival<P>> out = new LinkedHashSet<>();
        for (Arrival<P> one : left) {
            for (Arrival<P> other : right) {
                P both = naming.join(one.path(), other.path());
                if (both == null) {
                    refused.any = true;
                    continue;
                }
                out.add(new Arrival<>(Truth.UNREAD, new Provenance<>(both,
                        one.provenance().completeness().and(other.provenance().completeness()))));
                if (out.size() > naming.mostArrivals()) {
                    return out;
                }
            }
        }
        return out;
    }

    /** What a value nothing forks is settled by, which is the same thing however it is written. */
    private Set<Arrival<P>> oneWay() {
        return one(Truth.UNREAD, whole(naming.nowhere()));
    }

    private Set<Arrival<P>> one(Truth value, Provenance<P> by) {
        return Set.of(new Arrival<>(value, by));
    }

    private Provenance<P> whole(P path) {
        return new Provenance<>(path, Completeness.COMPLETE);
    }

    /** Whether a way was put aside because nothing takes it, which is not the same as none. */
    private static final class Refusals {
        private boolean any;
    }

    // ------------------------------------------------------------------- the tree

    /** Whether the operator settles its answer without evaluating both sides. */
    public static boolean shortCircuits(Hir.BinOp op) {
        return op == Hir.BinOp.AND || op == Hir.BinOp.OR;
    }

    /** Whether the operator answers with which way two values came out against each other. */
    public static boolean compares(Hir.BinOp op) {
        return switch (op) {
            case EQ, NE, LT, LE, GT, GE -> true;
            case AND, OR, ADD, SUB, MUL, DIV, CONCAT -> false;
        };
    }

    /**
     * Every value this node is built out of, in the order it is written.
     *
     * <p>Exhaustive and with no fallback. A node kind added to the IR should stop here and be
     * decided about rather than fall in with the ones every part of which is evaluated whenever the
     * node is.
     */
    private static List<Core> partsOf(Core node) {
        return switch (node) {
            case Core.Int ignored -> List.of();
            case Core.Decimal ignored -> List.of();
            case Core.Str ignored -> List.of();
            case Core.Bool ignored -> List.of();
            case Core.Temporal ignored -> List.of();
            case Core.Read ignored -> List.of();
            case Core.UnitValue ignored -> List.of();
            case Core.OptionNone ignored -> List.of();
            case Core.Unreachable ignored -> List.of();
            case Core.Neg neg -> present(neg.operand());
            case Core.FieldAccess access -> present(access.target());
            case Core.TupleGet get -> present(get.tuple());
            case Core.OptionSome option -> present(option.value());
            case Core.Binary binary -> present(binary.left(), binary.right());
            // The callee's own body is not read; its arguments are evaluated before it is reached.
            case Core.Call call -> call.args();
            case Core.PreservedCall call -> call.args();
            case Core.Apply apply -> apply.args();
            case Core.ListLit list -> list.elements();
            case Core.Tuple tuple -> tuple.elements();
            case Core.Construct construct ->
                    construct.values().stream().map(Core.FieldValue::value).toList();
            case Core.If iff -> present(iff.cond(), iff.then(), iff.els());
            case Core.LetIn let -> present(let.value(), let.body());
            // Not the body. Evaluating this makes the function.
            case Core.Block ignored -> List.of();
            case Core.Match match -> {
                List<Core> out = new ArrayList<>();
                out.add(match.scrutinee());
                match.cases().forEach(each -> out.add(each.body()));
                yield out;
            }
            case Core.IfConstructed constructed -> {
                List<Core> out = new ArrayList<>();
                out.add(constructed.construct());
                out.add(constructed.then());
                constructed.els().forEach(arm -> out.add(arm.body()));
                yield out;
            }
        };
    }

    /**
     * The parts that are there.
     *
     * <p>A body the checker refused a clause of arrives with a hole where the clause was, and a
     * reading that is not the checker has nothing to say about it. Used where the parts are read
     * together and not where they are numbered — an arm's place among the arms is what says which
     * way the fork came out, and a list with the missing one taken out would call the second arm the
     * first.
     */
    private static List<Core> present(Core... parts) {
        List<Core> out = new ArrayList<>();
        for (Core each : parts) {
            if (each != null) {
                out.add(each);
            }
        }
        return out;
    }
}
