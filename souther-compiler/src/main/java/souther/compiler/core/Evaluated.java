package souther.compiler.core;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

/**
 * What an expression evaluates, in the order it evaluates them.
 *
 * <p>One account of evaluation order, for the readers that need one. Which reason an arm aborts
 * with and which fork a body reaches first are two questions about the same order, and each working
 * it out for itself is two chances to disagree about what runs before what.
 *
 * <p><b>Not a list, because not every part runs.</b> {@code &&} and {@code ||} stop as soon as the
 * answer is settled (spec §a-condition-stops-when-its-answer-is-settled): the right operand of
 * {@code x /= 0 && 100 / x > 1} runs on the runs where the left came out true and on no others. A
 * sequence cannot say that, and said as a sequence it is wrong in both directions at once — what the
 * right operand does is taken as done on every run, and what it aborts on is taken as aborting every
 * run. So a step says whether anything decides that it runs.
 *
 * <p>Which was here to be got wrong before anything read it. {@link Step.OnlyWhere} exists because
 * the walk that judges constructions now carries what one step leaves into the next, and a step it
 * takes as running on every run is one it stops the walk at.
 *
 * <p><b>Strict positions only, and exhaustive.</b> A branch, an arm, a binding's body and a
 * departure are not evaluated by reaching the node they are written in — reaching it evaluates what
 * decides which of them runs, and each of them is entered by whoever owns it under what choosing it
 * settles. So what comes back for such a node is the part that runs whenever the node does, and no
 * more. A node kind added to the IR stops here and is decided about rather than falling in with the
 * ones every part of which is evaluated.
 *
 * <p>Not {@link Core#forEachChild}, which hands over the slots of a node and is not an account of
 * evaluation. The two differ at a construction: the emitter walks the declared fields and picks
 * each one's initializer out, so what runs first is the field declared first and not the one
 * written first.
 *
 * <p>A {@code Block} is a function value: evaluating that position makes the function, and its body
 * runs when a call applies it, on arguments this position does not have.
 */
public final class Evaluated {

    /** One thing an expression evaluates, and what decides that it is evaluated. */
    public sealed interface Step {

        /** What runs. */
        Core expression();

        /** Evaluated whenever the expression it is a step of is. */
        record Always(Core expression) implements Step {}

        /**
         * Evaluated only on the runs where {@code asked} came out {@code comesOut} — which is what
         * a short-circuiting operator's right operand is, and the only thing that is one today.
         *
         * <p>The condition is carried rather than the operator, because what a reader needs is what
         * has to hold for this to run. Handed the operator instead, every reader would work the
         * polarity out again, and {@code ||} is the one they would get wrong.
         */
        record OnlyWhere(Core asked, boolean comesOut, Core expression) implements Step {}
    }

    /**
     * Whether evaluating {@code e} makes a function and runs nothing of its body, which is so of
     * a closure however it is standing. A reader that files what a run works out in order asks
     * this of each thing it files, so that a closure written on the way is not filed as work.
     */
    public static boolean makesAFunction(Core e) {
        return Core.withoutStanding(e) instanceof Core.Block;
    }

    /** The sub-expressions of {@code e} that run, in the order they run. */
    public static List<Step> inOrder(Core e) {
        return switch (e) {
            case Core.Int _ -> List.of();
            case Core.Decimal _ -> List.of();
            case Core.Str _ -> List.of();
            case Core.Bool _ -> List.of();
            case Core.Temporal _ -> List.of();
            case Core.Read _ -> List.of();
            case Core.UnitValue _ -> List.of();
            case Core.OptionNone _ -> List.of();
            // Answers nothing and aborts, and evaluates nothing on its way there.
            case Core.Unreachable _ -> List.of();
            // Evaluates the value's body, which is its template's and not a part of this node.
            case Core.MaterialisedValue _ -> List.of();
            case Core.Neg neg -> always(neg.operand());
            case Core.FieldAccess access -> always(access.target());
            // What the names are read off; reading a name runs nothing of its own.
            case Core.FieldProjection projection -> always(projection.base());
            case Core.TupleGet get -> always(get.tuple());
            case Core.OptionSome option -> always(option.value());
            // What it holds runs; standing as a wider type runs nothing of its own.
            case Core.Widen widen -> always(widen.value());
            // The left, and then the right on the runs the left did not answer for. A false left
            // is the answer of a `&&` and a true left is the answer of an `||`, so what has to hold
            // for the right to run is the left coming out the other way.
            case Core.Binary binary when binary.op().stopsWhenItsAnswerIsSettled() ->
                    binary.left() == null || binary.right() == null
                            // A hole where an operand was. The left runs if it is there, and
                            // without a left to come out one way nothing decides the right — so it
                            // is not placed rather than placed wrongly. A body with a hole in it is
                            // one a clause was refused of, and every reading of it is already
                            // reading around what is missing.
                            ? always(binary.left())
                            : List.of(new Step.Always(binary.left()),
                                    new Step.OnlyWhere(binary.left(),
                                            binary.op().rightRunsWhenLeftIs(), binary.right()));
            case Core.Binary binary -> always(binary.left(), binary.right());
            // The callee's own body is not read; its arguments are evaluated before it is reached.
            case Core.Call call -> always(call.args());
            case Core.PreservedCall call -> always(call.args());
            // What is applied is a name holding a function, which is loaded and not run here.
            case Core.Apply apply -> always(apply.args());
            case Core.ListLit list -> always(list.elements());
            case Core.Tuple tuple -> always(tuple.elements());
            case Core.Construct construct ->
                    always(construct.values().stream().map(Core.FieldValue::value).toList());
            case Core.Block _ -> List.of();
            // What decides which branch, which arm, or whether the value was built. The branches and
            // the arms are entered by whoever owns them, under what choosing one settles.
            case Core.If iff -> always(iff.cond());
            case Core.LetIn let -> always(let.value());
            case Core.Match match -> always(match.scrutinee());
            // What the value is built of, and not the building: whether it is built is what the
            // attempt decides, as a condition decides an `if`, and a value its type refuses takes
            // the other arm and ends no run. So the construction is no value a run works out on
            // its way and gets past, which is what a step is; asked of a step, it would read a
            // refused attempt as a run that got past what the type asks.
            case Core.IfConstructed constructed -> inOrder(constructed.construct());
        };
    }

    /**
     * Whether {@code part}, a node of {@code root}'s tree, runs on every evaluation of
     * {@code root}: it is reached from {@code root} through steps that always run, or through the
     * body of a {@code let}, which runs once its value has whatever the value is.
     *
     * <p>Not through a branch, an arm, a right operand that runs only where the left comes out one
     * way, or the body of a function value: each of them is entered on some evaluations and not on
     * others. Asked by identity, so one node written twice is asked about where it stands.
     */
    public static boolean runsWhenever(Core root, Core part) {
        Core sought = Core.withoutStanding(part);
        return eachRunningWhenever(root, node -> node == sought);
    }

    /**
     * Every node of {@code root}'s tree that runs on every evaluation of it
     * ({@link #runsWhenever}), as it stands bare, into {@code into}: for a reader asking the same
     * of many parts, which a walk for each would go down the tree as many times.
     */
    public static void runningWhenever(Core root, Set<Core> into) {
        eachRunningWhenever(root, node -> {
            into.add(node);
            return false;
        });
    }

    /**
     * Hands {@code visit} each node of {@code root}'s tree that runs whenever {@code root} does,
     * bare, until it answers true, and says whether it did: the one account of which parts those
     * are, for both questions above.
     */
    private static boolean eachRunningWhenever(Core root, Predicate<Core> visit) {
        Core bare = Core.withoutStanding(root);
        if (visit.test(bare)) {
            return true;
        }
        if (bare instanceof Core.LetIn let && eachRunningWhenever(let.body(), visit)) {
            return true;
        }
        for (Step each : inOrder(root)) {
            if (each instanceof Step.Always(Core expression)
                    && eachRunningWhenever(expression, visit)) {
                return true;
            }
        }
        return false;
    }

    /**
     * The nodes of {@code roots}, worked out one after another, that a run takes the step of only
     * after it has taken the step of {@code site}: what a run stopping at {@code site} has not
     * got to. A node's own step comes after what it is made of, so every node {@code site} is in
     * is among them, and so is what is worked out past it, whether it stands in a later operand,
     * an arm or the right of an operator that may settle: that is worked out after what decides
     * it, which {@code site} is in or is not.
     *
     * <p>What is not among them may be worked out before {@code site}: a node is left out unless
     * every place a run may work it out at is after it. {@code site} is one node found in one
     * place; where it is not, or is in two, nothing is known to be after it.
     *
     * @param roots the expressions, in the order a run works them out
     */
    public static Set<Core> workedOutAfter(List<Core> roots, Core site) {
        if (site == null) {
            return Set.of();
        }
        After walk = new After(Core.withoutStanding(site));
        roots.forEach(walk::visit);
        return walk.after();
    }

    /** One walk in the order a run works the nodes out, with whether {@code site} has been taken. */
    private static final class After {

        private final Core site;
        private boolean taken;
        private int times;
        private final Set<Core> metBefore = Collections.newSetFromMap(new IdentityHashMap<>());
        private final Set<Core> metAfter = Collections.newSetFromMap(new IdentityHashMap<>());
        private final Set<Core> after = Collections.newSetFromMap(new IdentityHashMap<>());
        private final Set<Core> notAfter = Collections.newSetFromMap(new IdentityHashMap<>());

        After(Core site) {
            this.site = site;
        }

        /** A node is walked once for each of the two states, so one held at many places is not
         *  walked once for each. */
        void visit(Core expression) {
            Core node = Core.withoutStanding(expression);
            if (!(taken ? metAfter : metBefore).add(node)) {
                return;
            }
            List<Core> steps = new ArrayList<>();
            for (Step each : inOrder(node)) {
                steps.add(Core.withoutStanding(each.expression()));
            }
            steps.forEach(this::visit);
            Core.forEachChild(node, child -> {
                if (!steps.contains(Core.withoutStanding(child))) {
                    visit(child);
                }
            });
            if (node == site) {
                times++;
                taken = true;
            } else {
                (taken ? after : notAfter).add(node);
            }
        }

        Set<Core> after() {
            if (times != 1) {
                return Set.of();
            }
            Set<Core> out = Collections.newSetFromMap(new IdentityHashMap<>());
            after.stream().filter(node -> !notAfter.contains(node)).forEach(out::add);
            return out;
        }
    }

    /**
     * The parts that are there, each a step that always runs.
     *
     * <p>A body the checker refused a clause of arrives with a hole where the clause was, and a
     * reading that is not the checker has nothing to say about it.
     */
    private static List<Step> always(Core... parts) {
        return always(Arrays.asList(parts));
    }

    private static List<Step> always(List<Core> parts) {
        List<Step> out = new ArrayList<>();
        for (Core each : parts) {
            if (each != null) {
                out.add(new Step.Always(each));
            }
        }
        return List.copyOf(out);
    }

    private Evaluated() {}
}
