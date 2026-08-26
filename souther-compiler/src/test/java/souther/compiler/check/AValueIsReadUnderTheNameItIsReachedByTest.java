package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.types.ReachName;
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
 * resolution began settling it; the value side asked {@link Hir.Var#name()}, which is the spelling —
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
    private static Hir.Module resolved(String source, Map<String, String> imported) {
        Ast.Module parsed = CstFrontend.parse(source);
        Map<String, ValueName.Helper> helpers =
                new LinkedHashMap<>(Resolve.Reachable.of(parsed).helpers());
        imported.forEach((bare, module) -> helpers.put(bare, new ValueName.Helper(module, bare)));
        Resolve.Resolution answered = Resolve.resolving(parsed, SyntaxSymbols.of(parsed, DefaultStdlib.get()),
                new Resolve.Values(
                        new Resolve.Reachable(parsed.name(), helpers, Map.of(), java.util.Set.of(), true, Map.of(),
                                java.util.Set.of()),
                        Resolve.Elsewhere.NONE));
        if (!answered.unresolved().isEmpty()) {
            throw answered.unresolved().get(0);
        }
        return answered.module();
    }

    /** The value {@code up} publishes, under the name a reader reaches it by — which is how it
     * arrives in a reader's table. */
    private static Hir.FnDef published() {
        Hir.Module up = resolved("""
                module up exposing ( standard )

                let standard = 100
                """, Map.of());
        return HelperInliner.helpersOf(up).get("standard")
                .reachedAs(new ReachName.OfModule(new ValueName.Helper("up", "standard")));
    }

    private static Set<String> read(Hir.Module m, String fn, Map<String, Hir.FnDef> table) {
        // Which reference reaches each of them: what a module took on says so itself, and what it
        // declared it reaches bare.
        Map<ReachName, String> heldAt = new LinkedHashMap<>();
        table.forEach((at, def) -> heldAt.put(def.takenOnAs() != null ? def.takenOnAs()
                : new ReachName.Bare(new ValueName.Helper(m.name(), def.name())), at));
        Set<String> out = new LinkedHashSet<>();
        ValueCycles.valuesRead(HelperInliner.helpersOf(m).get(fn).writtenBody(), table,
                reference -> heldAt.get(reference) == null ? null
                        : new souther.compiler.ast.DefinitionName(heldAt.get(reference)),
                out);
        return out;
    }

    /**
     * The author wrote {@code standard}; the table holds {@code up.standard}. The reference carries
     * which of the two it reaches, and reading its spelling instead answers with a miss — silently,
     * because that is what a table does with a key it has not got.
     */
    @Test
    void aPublishedValueWrittenBareIsFoundUnderTheNameItIsReachedBy() {
        Hir.Module down = resolved("""
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
        Hir.Module solo = resolved("""
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
        Hir.Module down = resolved("""
                module down

                let twice (n: Int) : Int = n + n
                let four = twice(2)
                """, Map.of());

        assertEquals(Set.of(), read(down, "four", HelperInliner.helpersOf(down)));
    }
}
