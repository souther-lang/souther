package souther.compiler.core;

import souther.compiler.conformance.ConformanceCorpus;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.test.ClosedWorldContract;

import org.junit.jupiter.api.Test;

import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Consumer;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Every body a check hands on to be emitted is typed the way a checked tree is, after the passes
 * that rewrite it on the way.
 *
 * <p>Two things are held of it. A slot holds a value of the type its node takes it at, which is
 * what {@link EverySlotHoldsWhatItsNodeTakesItAsTest} holds of the trees checking hands out. And a
 * read of a binding is of the type the binding is in force at, which is what a pass that changes
 * what a binding stands for owes every read of it: the slot rule alone passes a read of the old
 * type standing under a {@link Core.Widen} to the new one.
 *
 * <p>A backend where element types are erased runs such a tree correctly whatever it says, so
 * nothing at run time asks this.
 */
@ClosedWorldContract
class EveryTreeTheBackendIsHandedIsTypedTest {

    @Test
    void everySlotHoldsWhatItsNodeTakesItAs() {
        List<String> found = new ArrayList<>();
        for (Core tree : trees()) {
            each(tree, node -> found.addAll(EverySlotHoldsWhatItsNodeTakesItAsTest.disagreements(
                    node)));
        }
        assertEquals(List.of(), found,
                "a slot of a body handed on to be emitted holding a value of a type other than the"
                        + " one its node takes it at");
    }

    @Test
    void everyReadIsOfTheTypeItsBindingIsInForceAt() {
        List<String> found = new ArrayList<>();
        for (Core tree : trees()) {
            reads(tree, found);
        }
        assertEquals(List.of(), found,
                "a read of a body handed on to be emitted at a type other than its binding's");
    }

    /**
     * And that the bodies read hold the walks a join wrote, where the outer step builds a list of
     * something other than what the walk reads — the join that puts the accumulator at a type the
     * inner step never had. A step binding its own accumulator to another name is the join's.
     */
    @Test
    void theCorpusHandsOnJoinedWalksThatChangeWhatTheyHold() {
        int[] joined = {0};
        for (Core tree : trees()) {
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
        assertFalse(joined[0] == 0,
                "no body the models hand on holds a joined walk that changes what it holds");
    }

    /**
     * And that the read rule reads what it says it reads: the joined walk of a {@code map} over a
     * {@code filter}, with its accumulator bound at the type the inner step had, disagrees.
     */
    @Test
    void aJoinedStepBoundAtTheInnerAccumulatorIsADisagreement() {
        Compilation c = Compilation.ofSource("""
                module demo
                behavior run : (xs: List<Int>) -> List<Bool>
                let run (xs) = List.map(n -> n > 0, List.filter(n -> n > 1, xs))
                """, "Main");
        Core body = c.db().ask(new Bodies.CheckedBehavior("demo", "run")).value().body();
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
        Compilation c = Compilation.ofSource("""
                module demo
                behavior run : (x: Int) -> Int
                let run (x) = match Int.truncatingDivide(x, 10) with
                    | Int as n -> n + 1
                    | DivisionByZero -> 0
                """, "Main");
        Core body = c.db().ask(new Bodies.CheckedBehavior("demo", "run")).value().body();
        List<Core.Match> matches = new ArrayList<>();
        each(body, node -> {
            if (node instanceof Core.Match m && m.cases().stream().anyMatch(a -> a.binder() != null)) {
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
            case Record part when part.getClass().getEnclosingClass() == Core.class -> {
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

    private static List<Core> trees;

    /**
     * Every body the models this repository carries hand on to be emitted: each behavior's, and
     * each definition a module's check emits as a method of its own — a helper, a value.
     *
     * <p>These are the answers of the queries that rewrite a checked body for the backend, which
     * {@code WhoMayRewriteACheckedBodyForTheBackendTest} in {@code souther-architecture-test} holds
     * to be the only ones. Every model and not only the conformance ones, which are written against
     * what the language declares and have no reason to write two walks in a row.
     */
    private static List<Core> trees() {
        if (trees != null) {
            return trees;
        }
        List<Core> out = new ArrayList<>();
        for (String name : ConformanceCorpus.manifest().keySet()) {
            ConformanceCorpus corpus = ConformanceCorpus.load(name);
            Map<String, String> byId = new LinkedHashMap<>();
            for (int i = 0; i < corpus.sources().size(); i++) {
                byId.put(corpus.files().get(i), corpus.sources().get(i));
            }
            Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
            c.answerEverything();
            for (String module : c.modules()) {
                Bodies.ModuleCheck.Of checkedModule =
                        c.db().ask(new Bodies.ModuleCheck(module)).value();
                if (checkedModule != null) {
                    checkedModule.emittedDefinitions().values()
                            .forEach(definition -> out.add(definition.body()));
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
                    }
                }
            }
        }
        trees = List.copyOf(out);
        return trees;
    }
}
