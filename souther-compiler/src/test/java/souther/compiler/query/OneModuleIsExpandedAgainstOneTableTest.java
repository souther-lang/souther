package souther.compiler.query;

import souther.compiler.ast.Hir;
import souther.compiler.check.HelperGraph;
import souther.compiler.check.HelperInliner;
import souther.compiler.check.HelperTable;
import souther.compiler.check.InliningPolicy;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.BindingOwner;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One module's bodies are expanded against one table, whoever asked for it.
 *
 * <p>Two callers build it. The check builds it from the settled module and the definitions its
 * imports publish, held apart ({@link HelperInliner#forModule}); {@link Bodies.Expanding} builds it
 * from {@link Bodies.ModuleDefinitions}, which is those two already joined, and hands the join over as what the
 * module has as fns of its own. So a definition another module publishes was one of this module's own
 * fns on one path and not on the other — and what a call expands to was decided by which caller was
 * asking.
 *
 * <p>What that decided is below: a spread of a published value is looked up among the module's own
 * fns, so the path that had it there substituted the value and the path that did not left the spread
 * standing. The check reads the second and the backend the first, which is one body under two
 * representations.
 */
class OneModuleIsExpandedAgainstOneTableTest {

    private static final String UP = """
            module up exposing ( Deal, standard )

            data Deal = { n: Int, amount: Int }

            let standard = Deal { n = 1, amount = 100 }
            """;

    private static final String DOWN = """
            module down

            import up ( Deal, standard )

            let raised (k: Int) : Deal = Deal { ...standard, amount = k }
            """;

    private static Db db() {
        return Compilation.ofDocuments(
                Map.of("up.sou", UP, "down.sou", DOWN), Set.of(), ModulePath.EMPTY).db();
    }

    /** The table the check expands against: the settled module, and what its imports publish beside
     * it — which is how {@link HelperInliner#forModule} is handed the two. */
    private static HelperTable asTheCheckBuildsIt(Db db, String module) {
        return HelperTable.of(db.ask(new Bodies.Settled(module)).value(),
                db.ask(new Bodies.ImportedDefinitions(module)).value(), InliningPolicy.FULL);
    }

    /** The table every query expands against, which the backend reads through. */
    private static HelperTable asTheQueryLayerBuildsIt(Db db, String module) {
        return db.ask(new Bodies.Expanding(module, InliningPolicy.FULL)).value().table();
    }

    @Test
    void theTableTheCheckExpandsAgainstIsTheTableTheQueryLayerExpandsAgainst() {
        Db db = db();
        assertEquals(asTheCheckBuildsIt(db, "down"), asTheQueryLayerBuildsIt(db, "down"));
    }

    @Test
    void aSpreadOfAPublishedValueIsSubstitutedWhicheverTableExpandsIt() {
        Db db = db();
        Hir.FnDef raised =
                HelperInliner.helpersOf(db.ask(new Bodies.Settled("down")).value()).get("raised");

        assertEquals(Set.of(), spreadsLeftBy(asTheCheckBuildsIt(db, "down"), raised),
                "the check left a published value standing as a spread");
        assertEquals(Set.of(), spreadsLeftBy(asTheQueryLayerBuildsIt(db, "down"), raised),
                "the query layer left a published value standing as a spread");
    }

    /** The names still written as spreads after {@code table} expands {@code fn}'s body. A value is
     * substituted where it is spread, so a name left here is one the expansion did not reach. */
    private static Set<String> spreadsLeftBy(HelperTable table, Hir.FnDef fn) {
        HelperInliner inliner = HelperInliner.over(table, HelperGraph.of(table));
        Hir.Expr expanded = inliner.inline(fn.writtenBody(),
                new BindingOwner.OfValue(table.module(), fn.name()));
        Set<String> left = new LinkedHashSet<>();
        namedSpreads(expanded, table, left);
        return left;
    }

    private static void namedSpreads(Hir.Expr e, HelperTable table, Set<String> out) {
        if (e instanceof Hir.NewData nd) {
            for (Hir.Var spread : nd.spreads()) {
                if (table.reaches(spread.reaches())) {
                    out.add(spread.reaches());
                }
            }
        }
        Hir.forEachChild(e, c -> namedSpreads(c, table, out));
    }

    /** And the module the two tables are built for is one the expansion has something to say about,
     * so neither passes by having nothing in it. */
    @Test
    void thePublishedValueIsThereToBeReached() {
        Db db = db();
        assertTrue(asTheCheckBuildsIt(db, "down").reaches("up.standard"));
        assertTrue(asTheQueryLayerBuildsIt(db, "down").reaches("up.standard"));
    }
}
