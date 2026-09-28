package souther.program.api;

import souther.compiler.Compiler;
import souther.compiler.core.Contract;
import souther.compiler.core.Core;
import souther.compiler.core.ValueShape;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.program.CheckedBehavior;
import souther.compiler.program.CheckedData;
import souther.compiler.program.CheckedHelper;
import souther.compiler.program.CheckedImplementation;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.program.CheckedValue;
import souther.compiler.program.CheckedValueEntry;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.WildcardType;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Consumer;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every {@code Core} a checked program hands out is a site {@link CheckedProgram#abortsAt} answers
 * for, and so is every node under one.
 *
 * <p>What the program is asked about is what an output emits, and an output emits whatever the
 * program hands it. The roots the answers are built over are a list the assembler keeps, and a list
 * kept beside the program's surface is one a new way of handing out {@code Core} would leave behind:
 * an output asking about a node under it would be refused as though the node were a stranger. So
 * the surface is read off the program's types here, and held to the places the list covers.
 */
class EveryCoreAProgramHandsOutIsASiteAbortsAtAnswersForTest {

    /**
     * Every public method reachable from a checked program whose answer holds a {@code Core},
     * named by the type that declares it. Each is walked by {@link #handedOut}, and the
     * assembler's roots cover each.
     */
    private static final Set<String> SURFACES = Set.of(
            "souther.compiler.program.CheckedImplementation$Body#body",
            "souther.compiler.program.CheckedHelper#body",
            "souther.compiler.program.CheckedValue#body",
            "souther.compiler.program.CheckedValueEntry#body",
            "souther.compiler.core.ValueShape$Invariant#condition",
            "souther.compiler.core.Contract$Rule#condition");

    private static final String PUBLISHED = """
            module lib.rates exposing ( Rate, rateFor )

            data Rate = Int
                invariant positive = value + 1 > 1

            behavior rateFor : (of: Int) -> Rate
            """;

    private static final String USES = """
            module app.uses exposing ( Span, Labelled, Tree, priced, halve, ys )
            import lib.rates ( Rate, rateFor )

            data Positive = Int
                invariant positive = value > 0

            data Span = { lo: Int, hi: Int }
                invariant ordered = hi - lo + 1 > 0

            data Labelled = { ...Span, label: String }

            let ks = [1, 2, 3]

            let ys = List.reverse(ks)

            data Tree = { n: Int, kids: List<Tree> }

            let flatten (t: Tree): List<Int> = [t.n] ++ List.flatMap(k -> flatten(k), t.kids)

            behavior priced : (base: Int, rate: Rate, t: Tree) -> Int
                ensures above = value + 1 > base

            let priced (base, rate, t) = base * rate.value + List.length(flatten(t)) + List.length(ys)

            behavior halve : (s: Labelled) -> Int

            let halve (s) = (s.hi - s.lo) * 2
            """;

    /**
     * The places a program hands out {@code Core} are exactly the ones the roots cover. A place
     * added to the program's surface fails this until the assembler's roots take it in and it is
     * named above.
     */
    @Test
    void theProgramHandsOutCoreOnlyWhereTheRootsLook() {
        assertEquals(new TreeSet<>(SURFACES), surfacesReachableFrom(CheckedProgram.class),
                "a place a checked program hands out Core that CheckedProgramAssembler's"
                        + " everyCoreRootOf does not take in, or one it no longer has");
    }

    /**
     * Every node under every {@code Core} the program hands out, one declared on the path and one
     * a spread took in among them, is answered for rather than refused.
     */
    @Test
    void everyNodeUnderEveryCoreHandedOutIsAnswered() {
        Map<String, ClassFileImage> published = Compiler.compile(PUBLISHED);
        CheckedProgram program = CheckedProgram.of(List.of(USES), ModulePath.of(published));

        Map<String, Core> roots = handedOut(program);
        List<String> refused = new ArrayList<>();
        for (Map.Entry<String, Core> root : roots.entrySet()) {
            each(root.getValue(), node -> {
                try {
                    program.abortsAt(node);
                } catch (IllegalArgumentException stranger) {
                    refused.add(root.getKey() + ": " + node);
                }
            });
        }

        assertEquals(List.of(), refused, "sites abortsAt does not answer for");
        for (String kind : List.of("body of", "helper", "value", "entry", "clause of lib.rates",
                "clause of app.uses.Labelled", "rule of")) {
            assertTrue(roots.keySet().stream().anyMatch(it -> it.startsWith(kind)),
                    () -> "nothing here reaches a " + kind + ", so this holds of none: "
                            + roots.keySet());
        }
    }

    /** Every {@code Core} the program hands out, through each of {@link #SURFACES}. */
    private static Map<String, Core> handedOut(CheckedProgram program) {
        Map<String, Core> roots = new LinkedHashMap<>();
        Set<CheckedData> data = new LinkedHashSet<>(program.languageDeclarations());
        for (CheckedModule module : program.modules()) {
            data.addAll(module.data());
            for (CheckedBehavior behavior : module.behaviors()) {
                if (behavior.implementation() instanceof CheckedImplementation.Body body) {
                    roots.put("body of " + behavior.name(), body.body());
                }
                Contract contract = behavior.ensures().contract();
                if (contract != null) {
                    for (Contract.Rule rule : contract.rules()) {
                        roots.put("rule of " + behavior.name() + " " + rule.clause(),
                                rule.condition());
                    }
                }
                List<Type> named = new ArrayList<>(behavior.signature().takes());
                named.add(behavior.signature().answers());
                for (Type type : named) {
                    if (type instanceof Type.Ref ref && ref.name() instanceof TypeSymbol.AtModule at) {
                        data.add(program.declaration(at).data());
                    }
                }
            }
            for (CheckedHelper helper : module.helpers()) {
                roots.put("helper " + helper.declares(), helper.body());
            }
            for (CheckedValue value : module.values()) {
                roots.put("value " + value.name(), value.body());
            }
            for (CheckedValueEntry entry : module.valueEntries()) {
                roots.put("entry " + entry.value(), entry.body());
            }
        }
        for (CheckedData declared : data) {
            if (declared instanceof CheckedData.WithFields fields) {
                List<ValueShape.Invariant> clauses = fields.invariants();
                for (int at = 0; at < clauses.size(); at++) {
                    roots.put("clause of " + declared.name() + " " + at,
                            clauses.get(at).condition());
                }
            }
        }
        return roots;
    }

    /** Every public method reachable from {@code from} whose answer names a {@code Core}. */
    private static Set<String> surfacesReachableFrom(Class<?> from) {
        Set<String> surfaces = new TreeSet<>();
        Set<Class<?>> seen = new HashSet<>();
        Deque<Class<?>> pending = new ArrayDeque<>();
        pending.add(from);
        while (!pending.isEmpty()) {
            Class<?> here = pending.poll();
            // What is under a Core is the Core's own, and walked as nodes rather than as a surface.
            if (!seen.add(here) || Core.class.isAssignableFrom(here)) {
                continue;
            }
            Class<?>[] arms = here.getPermittedSubclasses();
            if (arms != null) {
                pending.addAll(List.of(arms));
            }
            for (Method method : here.getMethods()) {
                if (method.getDeclaringClass() == Object.class) {
                    continue;
                }
                Set<Class<?>> named = new LinkedHashSet<>();
                namedIn(method.getGenericReturnType(), named);
                for (Class<?> each : named) {
                    if (Core.class.isAssignableFrom(each)) {
                        surfaces.add(method.getDeclaringClass().getName() + "#" + method.getName());
                    }
                    pending.add(each);
                }
            }
        }
        return surfaces;
    }

    private static void namedIn(java.lang.reflect.Type type, Set<Class<?>> into) {
        switch (type) {
            case Class<?> c -> {
                Class<?> element = c;
                while (element.isArray()) {
                    element = element.getComponentType();
                }
                if (element.getName().startsWith("souther.")) {
                    into.add(element);
                }
            }
            case ParameterizedType p -> {
                namedIn(p.getRawType(), into);
                for (java.lang.reflect.Type argument : p.getActualTypeArguments()) {
                    namedIn(argument, into);
                }
            }
            case WildcardType w -> {
                for (java.lang.reflect.Type bound : w.getUpperBounds()) {
                    namedIn(bound, into);
                }
            }
            default -> { }
        }
    }

    private static void each(Core node, Consumer<Core> visit) {
        visit.accept(node);
        Core.forEachChild(node, child -> each(child, visit));
    }
}
