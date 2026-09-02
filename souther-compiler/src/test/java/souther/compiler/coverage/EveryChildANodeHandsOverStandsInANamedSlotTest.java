package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.conformance.ConformanceCorpus;
import souther.compiler.core.Core;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The slots {@link CoreStructure} names are the children a node has, and no two of them are one
 * slot.
 *
 * <p>Two walks of the IR, and the whole of what makes the second one worth having is that it meets
 * the same children. {@link Core#forEachChild} is derived from the one switch that says which slots
 * a node has, so a node kind either walk forgot is a compile error in that switch; what neither the
 * language nor the compiler notices is this one handing over a different set, or the same set in a
 * different order, or two children under one name. Each of those makes an address of a place either
 * wrong or not an address at all — the third silently, since a path is a list of slots and a slot
 * that stood for two children stands for neither.
 *
 * <p>Asked of the bodies the conformance corpora compile to, which is what the compiler is held to
 * elsewhere, rather than of a model written to have one of everything. A model like that says what
 * its author remembered to put in it.
 */
class EveryChildANodeHandsOverStandsInANamedSlotTest {

    @Test
    void theNamedSlotsAreTheChildrenTheNodeHandsOver() {
        int nodes = 0;
        for (Core body : bodies()) {
            nodes += walk(body, node -> {
                List<Core> named = CoreStructure.childrenOf(node).stream()
                        .map(CoreStructure.Child::node).toList();
                List<Core> handed = new ArrayList<>();
                Core.forEachChild(node, handed::add);

                assertEquals(handed.size(), named.size(),
                        () -> node.getClass().getSimpleName() + " at " + node.pos()
                                + " hands over " + handed.size() + " children and has "
                                + named.size() + " named slots");
                for (int i = 0; i < handed.size(); i++) {
                    assertSame(handed.get(i), named.get(i),
                            "the child in slot " + i + " of a "
                                    + node.getClass().getSimpleName() + " at " + node.pos());
                }
            });
        }
        assertTrue(nodes > 0, "no body was walked at all, so this says nothing");
    }

    @Test
    void noNodeHandsOverTwoChildrenUnderOneSlot() {
        for (Core body : bodies()) {
            walk(body, node -> {
                List<CoreStructure.Child> children = CoreStructure.childrenOf(node);
                Set<CoreStructure.Edge> slots = new LinkedHashSet<>();
                children.forEach(child -> slots.add(child.edge()));
                assertEquals(children.size(), slots.size(),
                        () -> "a " + node.getClass().getSimpleName() + " at " + node.pos()
                                + " puts two children in one slot: " + children.stream()
                                        .map(CoreStructure.Child::edge).toList());
            });
        }
    }

    /**
     * How much of the vocabulary the two above are about.
     *
     * <p>Both of them hold of whatever they meet, so what they are worth is which slots that is.
     * Written down rather than counted, and written as what is met rather than as what ought to be:
     * a slot nothing here reaches is not a fault, and a slot that stops being reached is something
     * to look at. Either way the list moves and somebody reads it.
     *
     * <p>Five are not reached. {@code PreservedArgument} stands in no body that runs — a preserved
     * call is what an analysis keeps and coverage numbering refuses one outright — so nothing that
     * compiles will ever put one here. {@code TupleElement} and {@code TupleSource} are of a shape
     * the models below do not write. {@code AppliedFunction} and {@code ApplyArgument} are for a
     * function value that is applied through a binding rather than spliced, which is what the
     * expansion these bodies go through leaves none of.
     */
    @Test
    void theseAreTheSlotsTheModelsReach() {
        Set<String> met = new TreeSet<>();
        for (Core body : bodies()) {
            walk(body, node -> CoreStructure.childrenOf(node)
                    .forEach(child -> met.add(child.edge().getClass().getSimpleName())));
        }

        assertEquals(List.of("BinaryLeft", "BinaryRight", "BlockBody", "CallArgument",
                        "ConstructedAttempt", "ConstructedElse", "ConstructedThen", "FieldTarget",
                        "FieldValue", "IfCondition", "IfElse", "IfThen", "LetBody", "LetValue",
                        "ListElement", "MatchCase", "MatchScrutinee", "NegOperand", "SomeValue"),
                List.copyOf(met),
                "which slots the models put something in, and so which slots the checks above are"
                        + " about");
    }

    /** Applies {@code at} to every node of {@code body}, once per node however many ways there are
     *  to it, and answers how many there were. */
    private static int walk(Core body, java.util.function.Consumer<Core> at) {
        Map<Core, Boolean> seen = new IdentityHashMap<>();
        return walk(body, at, seen);
    }

    private static int walk(Core e, java.util.function.Consumer<Core> at, Map<Core, Boolean> seen) {
        if (seen.put(e, Boolean.TRUE) != null) {
            return 0;
        }
        at.accept(e);
        int count = 1;
        for (CoreStructure.Child child : CoreStructure.childrenOf(e)) {
            count += walk(child.node(), at, seen);
        }
        return count;
    }

    private static final String BESIDE_THE_CORPORA = """
            module demo

            data Warm = Int invariant hot = value >= 240
            data Low
            data Box = { held: Int }

            let picked (n: Int): List<Int> = [ n | n >= 240, n <= 300 ]

            behavior attempt : (t: Int) -> Warm | Low
                constructs Warm
            let attempt (t) = if Warm(t) as w then w else Low

            behavior over : (a: Int, b: Int) -> List<Int>
            let over (a, b) = picked(a) ++ picked(b)

            behavior negated : (n: Int) -> Int
            let negated (n) = -n + 1

            behavior boxed : (n: Int) -> Box
                constructs Box
            let boxed (n) = Box { held = n }

            behavior listed : (n: Int) -> List<Int>
            let listed (n) = [ n, n + 1 ]

            behavior kept : (xs: List<Int>) -> List<Int>
            let kept (xs) = List.filter(x -> x >= 240, xs)

            data Held = { at: Int? }

            behavior optional : (n: Int) -> Held
                constructs Held
            let optional (n) = Held { at = n }
            """;

    /** Every behavior body the conformance corpora compile to, and one model beside them. */
    private static List<Core> bodies() {
        List<Core> out = new ArrayList<>();
        List<List<String>> sources = new ArrayList<>();
        ConformanceCorpus.all().forEach(corpus -> sources.add(corpus.sources()));
        sources.add(List.of(BESIDE_THE_CORPORA));
        for (List<String> each : sources) {
            Compilation compilation = Compilation.ofSources(each, ModulePath.EMPTY);
            compilation.answerEverything();
            int before = out.size();
            for (String module : compilation.modules()) {
                Bodies.Elaborated checked =
                        compilation.db().ask(new Bodies.Checked(module)).value();
                if (checked != null) {
                    out.addAll(checked.behaviorBodies().values());
                }
            }
            // A source set that did not check contributes nothing, and would leave everything below
            // saying less than it says it does while staying green. Refused rather than skipped.
            assertTrue(out.size() > before,
                    () -> "a source set compiled to no body at all: " + compilation.errors());
        }
        assertFalse(out.isEmpty(), "no corpus compiled, so nothing below says anything");
        return out;
    }
}
