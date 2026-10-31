package souther.compiler.core;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Consumer;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every body a check hands on to be emitted is typed the way a checked tree is, after the passes
 * that rewrite it on the way, on models that each raise one thing the rule is about: a kernel
 * handed an argument narrower than it takes, a walk joined to another that changes what it holds,
 * and a binding an arm makes.
 *
 * <p>Two things are held of a tree. A slot holds a value of the type its node takes it at
 * ({@link WhatASlotHoldsAgainstWhatItsNodeTakesItAs}), which is what
 * {@link EverySlotHoldsWhatItsNodeTakesItAsTest} holds of the trees checking hands out. And a read
 * of a binding is of the type the binding is in force at, which is what a pass that changes what a
 * binding stands for owes every read of it.
 */
class TheTreesOfAModelTheBackendIsHandedAreTypedTest {

    /** A kernel handed an argument narrower than it takes: the rounding mode is a case of its
     *  type. */
    private static final String ROUNDS = """
            module demo
            behavior run : (d: Decimal) -> Decimal
            let run (d) = Decimal.round(2, HALF_UP, d)
            """;

    /** Two walks in a row, the outer of which builds a list of something other than what the
     *  inner reads. */
    private static final String JOINS = """
            module demo
            behavior run : (xs: List<Int>) -> List<Bool>
            let run (xs) = List.map(n -> n > 0, List.filter(n -> n > 1, xs))
            """;

    /** A binding an arm makes, and a read of it. */
    private static final String BINDS = """
            module demo
            behavior run : (x: Int) -> Int
            let run (x) = match Int.truncatingDivide(x, 10) with
                | Int as n -> n + 1
                | DivisionByZero -> 0
            """;

    /** A helper that calls itself and a value of the module, which are emitted as methods of their
     *  own and not into the behavior that calls them. */
    private static final String DEFINES = """
            module demo
            partial let total (n: Int): Int = if n <= 0 then 0 else n + total(n - 1)
            let limit = List.length([1, 2, 3])
            behavior run : (n: Int) -> Int
            let run (n) = total(n) + limit
            """;

    private static Compilation compiled(String source) {
        return Compilation.ofSource(source, "Main");
    }

    private static List<Core> trees() {
        return treesOf(List.of(compiled(ROUNDS), compiled(JOINS), compiled(BINDS),
                compiled(DEFINES)));
    }

    /** And that what a module's check emits as a method of its own is among the trees read, so the
     *  rules above are asked of the definitions as well as of the behaviors. */
    @Test
    void aModelHandsOnTheDefinitionsItsModuleEmits() {
        Compilation c = compiled(DEFINES);
        Bodies.ModuleCheck.Of checked = c.db().ask(new Bodies.ModuleCheck("demo")).value();
        assertFalse(checked.emittedDefinitions().isEmpty(),
                "the module emits no definition of its own, so none is read");
        List<Core> read = treesOf(List.of(c));
        for (var definition : checked.emittedDefinitions().values()) {
            assertTrue(read.contains(definition.body()),
                    () -> "a definition the module emits is not among the trees read");
        }
        assertEquals(List.of(), slotDisagreements(read));
        assertEquals(List.of(), readDisagreements(read));
    }

    @Test
    void everySlotHoldsWhatItsNodeTakesItAs() {
        assertEquals(List.of(), slotDisagreements(trees()),
                "a slot of a body handed on to be emitted holding a value of a type other than the"
                        + " one its node takes it at");
    }

    /** And that the body read applies a kernel to an argument narrower than the application takes,
     *  so the slot rule is asked of a Widen among a kernel's arguments. */
    @Test
    void aModelHandsOnAKernelAppliedToAnArgumentItWidens() {
        int[] counts = kernelsAppliedAndWidened(treesOf(List.of(compiled(ROUNDS))));
        assertFalse(counts[0] == 0, "no body the model hands on applies a kernel to an argument");
        assertFalse(counts[1] == 0,
                "no body the model hands on hands a kernel an argument narrower than it takes");
    }

    @Test
    void everyReadIsOfTheTypeItsBindingIsInForceAt() {
        assertEquals(List.of(), readDisagreements(trees()),
                "a read of a body handed on to be emitted at a type other than its binding's");
    }

    /** And that the body read holds the walk a join wrote, where the outer step builds a list of
     *  something other than what the walk reads. */
    @Test
    void aModelHandsOnAJoinedWalkThatChangesWhatItHolds() {
        assertFalse(joinedWalksThatChangeWhatTheyHold(treesOf(List.of(compiled(JOINS)))) == 0,
                "no body the model hands on holds a joined walk that changes what it holds");
    }

    /**
     * And that the read rule reads what it says it reads: the joined walk of a {@code map} over a
     * {@code filter}, with its accumulator bound at the type the inner step had, disagrees.
     */
    @Test
    void aJoinedStepBoundAtTheInnerAccumulatorIsADisagreement() {
        Compilation c = compiled(JOINS);
        Core built = c.db().ask(new Bodies.CheckedBehavior("demo", "run")).value().body();
        Core body = GrowingFold.joins(built, Scopes.resolved(c.db(), "demo").value().theWalk());
        List<Core.Block> steps = new ArrayList<>();
        each(body, node -> {
            if (node instanceof Core.Call call && call.fn() == Core.Emitted.BUILD_LIST) {
                steps.add((Core.Block) Core.withoutStanding(call.args().getFirst()));
            }
        });
        assertEquals(1, steps.size(), "the two walks are one: " + steps);
        Core.Block step = steps.getFirst();
        Core.Block stale = new Core.Block(step.params(),
                List.of(new Type.ListOf(Type.INT), step.paramTypes().get(1)), step.body(),
                step.pos());
        List<String> found = new ArrayList<>();
        reads(stale, found);
        assertFalse(found.isEmpty(), "the accumulator bound at the list in between");
    }

    /**
     * And that a binding form the walk does not enter is not taken for one bound outside the tree:
     * a read under an arm's binding, walked as though the arm bound nothing, is out of scope.
     */
    @Test
    void aReadUnderABindingTheWalkDoesNotEnterIsADisagreement() {
        Compilation c = compiled(BINDS);
        Core body = c.db().ask(new Bodies.CheckedBehavior("demo", "run")).value().body();
        List<Core.Match> matches = new ArrayList<>();
        each(body, node -> {
            if (node instanceof Core.Match m
                    && m.cases().stream().anyMatch(a -> a.binder() != null)) {
                matches.add(m);
            }
        });
        assertFalse(matches.isEmpty(), "the match binds what it found");
        Core.Case arm = matches.getFirst().cases().stream()
                .filter(a -> a.binder() != null).findFirst().orElseThrow();
        Set<BindingId> held = new HashSet<>();
        each(body, node -> held(node, held));
        List<String> found = new ArrayList<>();
        reads(arm.body(), new HashMap<>(), held, found);
        assertFalse(found.isEmpty(), "the arm's binding, read with the arm not entered");
    }

    /** The slots of {@code trees} holding a value of a type other than the one their node takes. */
    private static List<String> slotDisagreements(List<Core> trees) {
        List<String> found = new ArrayList<>();
        for (Core tree : trees) {
            each(tree, node -> found.addAll(
                    WhatASlotHoldsAgainstWhatItsNodeTakesItAs.disagreements(node)));
        }
        return found;
    }

    /** How many kernel applications {@code trees} hold, and how many of them hand a kernel an
     *  argument narrower than it takes. */
    private static int[] kernelsAppliedAndWidened(List<Core> trees) {
        int[] counts = {0, 0};
        for (Core tree : trees) {
            each(tree, node -> {
                if (node instanceof Core.Call call
                        && call.settlement() instanceof Core.CallSettlement.AtKernel
                        && !call.args().isEmpty()) {
                    counts[0]++;
                    if (call.args().stream().anyMatch(Core.Widen.class::isInstance)) {
                        counts[1]++;
                    }
                }
            });
        }
        return counts;
    }

    /** The reads of {@code trees} at a type other than the one their binding is in force at. */
    private static List<String> readDisagreements(List<Core> trees) {
        List<String> found = new ArrayList<>();
        for (Core tree : trees) {
            reads(tree, found);
        }
        return found;
    }

    /** How many joined walks {@code trees} hold that change what they hold: the outer step builds
     *  a list of something other than what the inner step reads. */
    private static int joinedWalksThatChangeWhatTheyHold(List<Core> trees) {
        int[] joined = {0};
        for (Core tree : trees) {
            each(tree, node -> {
                if (node instanceof Core.Call call && call.fn() == Core.Emitted.BUILD_LIST
                        && Core.withoutStanding(call.args().getFirst()) instanceof Core.Block step
                        && bindsTheAccumulator(step)
                        && step.paramTypes().getFirst() instanceof Type.ListOf built
                        && !built.element().equals(step.paramTypes().get(1))) {
                    joined[0]++;
                }
            });
        }
        return joined[0];
    }

    private static boolean bindsTheAccumulator(Core.Block step) {
        BindingId acc = step.params().getFirst().binding();
        boolean[] found = {false};
        each(step.body(), node -> found[0] |= node instanceof Core.LetIn let
                && Core.withoutStanding(let.value()) instanceof Core.Read v
                && v.binding().equals(acc));
        return found[0];
    }

    /**
     * Each read in {@code tree} that is not of the type its binding is in force at, or that reads a
     * binding the tree holds from somewhere that binding is not in force.
     *
     * <p>The second is what keeps this from passing a binding form it does not know. Which bindings
     * the tree holds is read off every node's components ({@link #held}) rather than off the forms
     * the walk below enters, so a form the walk left out has its reads come up as out of scope
     * instead of as reads of something bound outside the tree. What is bound outside it — a
     * behavior's or a method's parameters — is held by no node here, and a read of it is asked
     * nothing.
     */
    private static void reads(Core tree, List<String> found) {
        Set<BindingId> held = new HashSet<>();
        each(tree, node -> held(node, held));
        reads(tree, new HashMap<>(), held, found);
    }

    private static void reads(Core e, Map<BindingId, Type> inForce, Set<BindingId> held,
                              List<String> found) {
        if (e == null) {
            return;
        }
        switch (e) {
            case Core.Read v -> {
                if (inForce.containsKey(v.binding())) {
                    Type bound = inForce.get(v.binding());
                    if (!bound.equals(v.type())) {
                        found.add(v.name() + " at " + v.pos() + " is read as "
                                + Type.show(v.type()) + " and bound at " + Type.show(bound));
                    }
                } else if (held.contains(v.binding())) {
                    found.add(v.name() + " at " + v.pos() + " is read where it is not bound");
                }
            }
            case Core.Block block -> {
                Map<BindingId, Type> inner = new HashMap<>(inForce);
                for (int i = 0; i < block.params().size(); i++) {
                    inner.put(block.params().get(i).binding(), block.paramTypes().get(i));
                }
                reads(block.body(), inner, held, found);
            }
            case Core.LetIn let -> {
                reads(let.value(), inForce, held, found);
                reads(let.body(), with(inForce, let.binder(), let.bindType()), held, found);
            }
            // What was built is bound where the invariant held, and nowhere else.
            case Core.IfConstructed attempt -> {
                reads(attempt.construct(), inForce, held, found);
                reads(attempt.then(), with(inForce, attempt.binder(),
                        attempt.construct().type()), held, found);
                attempt.els().forEach(arm -> reads(arm.body(), inForce, held, found));
            }
            case Core.Match match -> {
                reads(match.scrutinee(), inForce, held, found);
                for (Core.Case arm : match.cases()) {
                    reads(arm.body(), arm.binder() == null ? inForce
                            : with(inForce, arm.binder(), arm.bindType()), held, found);
                }
            }
            default -> Core.forEachChild(e, child -> reads(child, inForce, held, found));
        }
    }

    private static Map<BindingId, Type> with(Map<BindingId, Type> inForce, Core.Binder binder,
                                             Type type) {
        Map<BindingId, Type> inner = new HashMap<>(inForce);
        inner.put(binder.binding(), type);
        return inner;
    }

    /**
     * Every binding {@code value} holds, found among its components and whatever parts of the tree
     * they hold short of another node — so an arm's binding is the match's, and a binding form added
     * to {@link Core} is found here without being named. A part of the tree is a record {@link Core}
     * declares; a type or a pattern is not one, and holds no binding.
     */
    private static void held(Object value, Set<BindingId> out) {
        switch (value) {
            case Core.Binder binder -> out.add(binder.binding());
            case List<?> list -> list.forEach(each -> held(each, out));
            case Record part when part.getClass().getEnclosingClass() == Core.class
                    || part instanceof Core.ArmBinding -> {
                for (RecordComponent component : part.getClass().getRecordComponents()) {
                    Object inside;
                    try {
                        inside = component.getAccessor().invoke(part);
                    } catch (ReflectiveOperationException e) {
                        throw new IllegalStateException(e);
                    }
                    if (!(inside instanceof Core)) {
                        held(inside, out);
                    }
                }
            }
            case null, default -> { }
        }
    }

    private static void each(Core e, Consumer<Core> f) {
        if (e == null) {
            return;
        }
        f.accept(e);
        Core.forEachChild(e, child -> each(child, f));
    }

    /**
     * Every body the models of {@code population} hand on to be emitted: each behavior's, and each
     * definition a module's check emits as a method of its own — a helper, a value.
     *
     * <p>These are the answers of the queries that rewrite a checked body for the backend, and the
     * form the backend emits them in where no run is recorded, which is the same bodies with the
     * walks they hold joined. {@code WhoMayRewriteACheckedBodyForTheBackendTest} in
     * {@code souther-architecture-test} holds those to be the only places a body is rewritten.
     */
    private static List<Core> treesOf(List<Compilation> population) {
        List<Core> out = new ArrayList<>();
        for (Compilation c : population) {
            for (String module : c.modules()) {
                TheWalk walk = Scopes.resolved(c.db(), module).value().theWalk();
                Bodies.ModuleCheck.Of checkedModule =
                        c.db().ask(new Bodies.ModuleCheck(module)).value();
                if (checkedModule != null) {
                    checkedModule.emittedDefinitions().values().forEach(definition -> {
                        out.add(definition.body());
                        out.add(GrowingFold.joins(definition.body(), walk));
                    });
                }
                Set<String> names = c.declaredBehaviors(module);
                if (names == null) {
                    continue;
                }
                for (String behavior : new TreeSet<>(names)) {
                    Bodies.CheckedBody checked =
                            c.db().ask(new Bodies.CheckedBehavior(module, behavior)).value();
                    if (checked != null && checked.body() != null) {
                        out.add(checked.body());
                        out.add(GrowingFold.joins(checked.body(), walk));
                    }
                }
            }
        }
        return List.copyOf(out);
    }
}
