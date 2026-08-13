package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A value a body reads is looked up by the name that body reaches it by, never by how it is spelled.
 *
 * <p>The value edges and the call edges are the two kinds of edge in one graph and are followed
 * together, so they have to be keyed alike. The call side has asked what a call reaches since
 * resolution began settling it; the value side asked {@link Ast.Var#name()}, which is the spelling —
 * and an import lets a name be written without its qualifier while the table keys it under the
 * module that declares it.
 *
 * <p>Nothing failed for it. {@code HelperNames.qualifyImports} writes an imported name out qualified
 * before any of the callers run, so the spelling had already been made into the key and the two
 * agreed. That is a pass covering for a lookup rather than a lookup that holds, so the shape is built
 * here rather than compiled from a file: a resolved body, which is what that pass is handed, reading a
 * published value under the bare name its author wrote.
 */
class AValueIsReadUnderTheNameItIsReachedByTest {

    /** {@code source} resolved with {@code imported} (bare name -> declaring module) reachable, which
     * is the tree {@code HelperNames.qualifyImports} is given — the author's spellings still on it. */
    private static Ast.Module resolved(String source, Map<String, String> imported) {
        Ast.Module parsed = CstFrontend.parse(source);
        Map<String, ValueName.Helper> helpers =
                new LinkedHashMap<>(Resolve.Values.of(parsed).helpers());
        imported.forEach((bare, module) -> helpers.put(bare, new ValueName.Helper(module, bare)));
        Resolve.Resolved answered = Resolve.resolving(parsed, Symbols.of(parsed),
                new Resolve.Values(parsed.name(), helpers, Map.of(), Map.of()));
        if (!answered.unresolved().isEmpty()) {
            throw answered.unresolved().get(0);
        }
        return answered.module().module();
    }

    /** The value {@code up} publishes, under the name a reader reaches it by — which is how it
     * arrives in a reader's table. */
    private static Ast.FnDef published() {
        Ast.Module up = resolved("""
                module up exposing ( standard )

                let standard = 100
                """, Map.of());
        return HelperInliner.helpersOf(up).get("standard").reachedAs("up.standard");
    }

    private static Set<String> read(Ast.Module m, String fn, Map<String, Ast.FnDef> table) {
        Set<String> out = new LinkedHashSet<>();
        ValueCycles.valuesRead(HelperInliner.helpersOf(m).get(fn).writtenBody(), table, out);
        return out;
    }

    /**
     * The author wrote {@code standard}; the table holds {@code up.standard}. The reference carries
     * which of the two it reaches, and reading its spelling instead answers with a miss — silently,
     * because that is what a table does with a key it has not got.
     */
    @Test
    void aPublishedValueWrittenBareIsFoundUnderTheNameItIsReachedBy() {
        Ast.Module down = resolved("""
                module down

                let doubled = standard + standard
                """, Map.of("standard", "up"));

        assertEquals(Set.of("up.standard"),
                read(down, "doubled", Map.of("up.standard", published())));
    }

    /** And a value of the module's own is reached bare, so it is still found under that. A reader
     * moved onto the reach name answers both, which is the point of there being one key. */
    @Test
    void aValueTheModuleDeclaresIsFoundUnderItsBareName() {
        Ast.Module solo = resolved("""
                module solo

                let base = 1
                let doubled = base + base
                """, Map.of());

        assertEquals(Set.of("base"),
                read(solo, "doubled", HelperInliner.helpersOf(solo)));
    }

    /** A helper is not a value, whatever it is keyed under: what closes a value cycle is a value, and
     * a call is the other kind of edge. So neither reading answers with one. */
    @Test
    void aHelperReachedByTheSameRouteIsStillNotAValue() {
        Ast.Module down = resolved("""
                module down

                let twice (n: Int) : Int = n + n
                let four = twice(2)
                """, Map.of());

        assertEquals(Set.of(), read(down, "four", HelperInliner.helpersOf(down)));
    }
}
