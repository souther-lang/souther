package souther.compiler.query;

import souther.compiler.check.Resolve;
import souther.compiler.check.Scoping;
import souther.compiler.types.ValueName;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Resolving a bare name and listing what may be written here are one question, and both read
 * {@link Resolve.Reachable#byName()}.
 *
 * <p>Written as agreement between the two answers rather than as the order the three tables are
 * consulted in. Within a legal module they are disjoint — a definition spelled like a name an import
 * brings in is refused where the import is written (E1508) — so an order is a rule no program
 * exercises, and a test that asserted one would pass over two readers that had already gone apart.
 * What can go apart is what each answers about a spelling, and that is what is held here.
 */
class ABareNameIsLookedUpInTheTableThatListsItTest {

    private static final String UP = """
            module up exposing ( price )

            let price = 100
            """;

    private static final String DOWN = """
            module down

            import up ( price )
            import String ( length )

            let own (n) = n + price

            behavior sizes : (s: String) -> Int
            let sizes (s) = own(length(s))

            behavior twice : (s: String) -> Int
            let twice (s) = sizes(s) + sizes(s)

            behavior double : (n: Int) -> Int
            let double (n) = n + n
            """;

    private static Compilation compiled() {
        return Compilation.ofDocuments(
                Map.of("file:///up.sou", UP, "file:///down.sou", DOWN), Set.of(),
                souther.compiler.meta.ModulePath.EMPTY);
    }

    private static Resolve.Reachable reachable(Compilation compilation) {
        Scoping.Scoped scoped = compilation.db().ask(new Names.ModuleScope("down")).value();
        assertTrue(scoped != null, "the module's scope is assembled");
        return scoped.reachable();
    }

    @Test
    void everyBareNameResolvesToWhatTheTableSaysItReaches() {
        Compilation compilation = compiled();
        Map<String, ValueName> byName = reachable(compilation).byName();
        Resolve.ResolutionIndex facts = compilation.db().ask(new Names.Facts("down")).value();
        assertTrue(facts != null, "the module resolves");

        List<String> checked = new ArrayList<>();
        for (Resolve.ValueUse use : facts.values()) {
            String written = use.written().canonical();
            ValueName listed = byName.get(written);
            if (listed == null) {
                continue;   // a binding in force, or a name written through its module
            }
            assertEquals(listed, use.denotes(),
                    "`" + written + "` is listed as reaching " + listed
                            + " and resolved to " + use.denotes());
            checked.add(written);
        }
        assertTrue(checked.containsAll(List.of("own", "price", "length", "sizes")),
                "a helper of this module, a value another module publishes, a library name an "
                        + "import brought in, and a behavior — each was resolved: " + checked);
    }

    /** Every way into the namespace arrives in the one table, so a reader listing what may be
     * written here does not have to know how many ways there are. */
    @Test
    void theTableHoldsWhatEachKindOfNameReaches() {
        Map<String, ValueName> byName = reachable(compiled()).byName();

        assertEquals(new ValueName.Helper("down", "own"), byName.get("own"));
        assertEquals(new ValueName.Helper("up", "price"), byName.get("price"),
                "a published value is reached bare, under the module that wrote it");
        assertEquals(new ValueName.Behavior("down", "sizes"), byName.get("sizes"));
        assertEquals(new ValueName.Stdlib("String", "length"), byName.get("length"));
        assertFalse(byName.containsKey("s"), "a binding in force is not in a module's table");
    }
}
