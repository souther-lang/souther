package souther.compiler.query;

import souther.compiler.Compiler;
import souther.compiler.check.HelperInliner;
import souther.compiler.check.Prepared;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row's operand is a definition of the module, so the helpers it names are expanded into it the
 * way they are expanded into any body. What the module takes on for a row is what expansion cannot
 * remove, which is a recursion and nothing else.
 *
 * <p>A row used to be read by machinery of its own, and a helper it named was applied through a
 * method emitted for that purpose. The operand is compiled as the module's own definition now, so
 * the call in it is an ordinary call and the expansion an ordinary expansion — and a method emitted
 * beside that is a method nothing invokes. Emitting one was not merely spare: it is why a module
 * came to hold another module's definition, and to report on it.
 *
 * <p>The recursion is the exception and is one for a reason that has nothing to do with rows. A
 * recursive helper is a method wherever it is reached, because expanding it would not terminate.
 * So the claim here is not "nothing is taken on for a row" but "what is taken on is exactly what
 * recurses", which is why every case is held against the recursions the module reaches rather than
 * against a list written out here.
 */
class ARowExpandsWhatItNamesAndTakesOnOnlyWhatItCannotTest {

    private static final String ORDINARY = """
            module rules exposing ( doubled )

            let doubled (n: Int) : Int = n * 2
            """;

    private static final String RECURSIVE = """
            module rules exposing ( Item, depth )

            data Item = { rank: Int, parent: Item? }

            let depth (i: Item) : Int =
                match i.parent with
                    | Some p -> 1 + depth(p)
                    | None   -> 0
            """;

    private static String app(String imported, String row) {
        return """
                module app exposing ( In, Out, run )

                import rules ( """ + imported + """
                 )

                data In  = { n: Int }
                data Out = { m: Int }

                behavior run : (i: In) -> Out constructs Out
                let run (i) = Out { m = i.n }

                example run
                """ + row;
    }

    /**
     * What {@code app} took on beyond the methods its own row operands are, and what it reaches that
     * recurses. The claim is that those are the same set.
     */
    private static Set<String> takenOnIsExactlyWhatRecurses(String rules, String imported,
                                                            String row) {
        Db db = Compilation.ofDocuments(Map.of("rules.sou", rules, "app.sou", app(imported, row)),
                Set.of(), ModulePath.EMPTY).db();
        Answer<Prepared> answer = db.ask(new Shapes.Prepared("app"));
        assertTrue(answer.present(), "prepared of app: " + answer.reports());
        Prepared state = answer.value();

        Set<String> beyond = new LinkedHashSet<>(HelperInliner.takenOnBy(state.tree()).keySet());
        beyond.removeAll(state.operandMethods().values());

        assertEquals(db.ask(new Bodies.RecursiveHelpers("app")).value(), beyond);
        return beyond;
    }

    @Test
    void anOrdinaryHelperARowNamesIsExpandedIntoTheOperandAndNotTakenOn() {
        takenOnIsExactlyWhatRecurses(ORDINARY, "doubled", """
                    | "a row applies a published helper" : (In { n = doubled(3) }) -> Out { m = 6 }
                """);
    }

    @Test
    void aLibraryKernelARowAppliesIsLoweredWhereItIsCalledAndNotWrapped() {
        takenOnIsExactlyWhatRecurses(ORDINARY, "doubled", """
                    | "a row applies a kernel" : (In { n = List.length([ 1, 2 ]) }) -> Out { m = 2 }
                """);
    }

    @Test
    void aRecursiveHelperARowNamesIsTakenOnBecauseExpansionCannotRemoveIt() {
        Set<String> beyond = takenOnIsExactlyWhatRecurses(RECURSIVE, "Item, depth", """
                    | "a row applies a recursion" : (In { n = depth(Item { rank = 0 }) }) -> Out { m = 0 }
                """);

        // And it is genuinely there: a claim that two sets agree says little if both are empty.
        assertTrue(beyond.contains("rules.depth"), beyond.toString());
    }

    @Test
    void andEachOfThoseRowsStillHolds() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(ORDINARY, app("doubled", """
                    | "a row applies a published helper" : (In { n = doubled(3) }) -> Out { m = 6 }
                """))));
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(ORDINARY, app("doubled", """
                    | "a row applies a kernel" : (In { n = List.length([ 1, 2 ]) }) -> Out { m = 2 }
                """))));
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(RECURSIVE, app("Item, depth", """
                    | "a row applies a recursion" : (In { n = depth(Item { rank = 0 }) }) -> Out { m = 0 }
                """))));
    }
}
