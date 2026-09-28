package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.frontend.CstFrontend;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * {@link HelperTable#reachable}'s own Javadoc makes its order part of what a table means — the
 * source {@link HelperGraph} and {@code Bodies.RequiredRecursiveDefs} both read it from. A {@link
 * java.util.Map}'s {@code equals} does not see order, so {@code HelperTable.equals} has to compare
 * {@code reachable()} as the sequence it is declared to be rather than hand it to {@code Map.equals}
 * directly (issue #1835's review: {@code SequencedMap} alone types the contract but does not enforce
 * it).
 *
 * <p>The two tables below are built from the exact same {@link Hir.FnDef} instances, handed to
 * {@link HelperTable#of} in reversed map order — not two separately parsed sources, whose
 * declarations would carry different positions and differ in content regardless of order, hiding
 * whether order on its own is what {@code equals} is catching.
 */
class ATablesReachableOrderIsPartOfItsEqualsTest {

    private static final String SOURCE = """
            module demo

            let alpha (n: Int) : Int = n
            let bravo (n: Int) : Int = n
            """;

    private static Map<String, Hir.FnDef> declaredOf(String source) {
        Ast.Module parsed = CstFrontend.parse(source);
        Hir.Module resolved = Resolve.module(parsed, SyntaxSymbols.of(parsed, DefaultStdlib.get()));
        return HelperInliner.helpersOf(resolved);
    }

    private static Map<String, Hir.FnDef> reversed(Map<String, Hir.FnDef> declared) {
        List<String> keys = new ArrayList<>(declared.keySet());
        Collections.reverse(keys);
        Map<String, Hir.FnDef> out = new LinkedHashMap<>();
        keys.forEach(key -> out.put(key, declared.get(key)));
        return out;
    }

    private static HelperTable tableOf(Map<String, Hir.FnDef> declared) {
        return HelperTable.of("demo", declared, Map.of(), Map.of(), InliningPolicy.FULL,
                DefaultStdlib.get());
    }

    @Test
    void reorderingTheSameDeclarationsChangesTheTable() {
        Map<String, Hir.FnDef> declared = declaredOf(SOURCE);
        HelperTable inOrder = tableOf(declared);
        HelperTable reversedOrder = tableOf(reversed(declared));

        assertNotEquals(inOrder, reversedOrder,
                "the exact same two declarations, reached under the same references, handed to"
                        + " HelperTable.of in reversed order: reachable()'s own contract says the"
                        + " order means something, so Map.equals — which does not see it — must"
                        + " not be the whole of HelperTable.equals");
    }

    @Test
    void theSameOrderIsStillEqual() {
        Map<String, Hir.FnDef> declared = declaredOf(SOURCE);
        assertEquals(tableOf(declared), tableOf(declared),
                "two tables built the same way from the same declarations must still compare"
                        + " equal, or every edit would look like a change to everything downstream");
    }
}
