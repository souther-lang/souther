package souther.compiler.query;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.check.ClosedImports;
import souther.compiler.check.HelperTable;
import souther.compiler.check.InliningPolicy;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.ReachName;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a module imports arrives closed under the policy the reader expands in, however many modules
 * it passed through.
 *
 * <p>A published body is expanded where it was written, so whatever that expansion resolved is gone
 * before a reader sees it. The tree an analysis reads leaves the language's operations standing
 * ({@link InliningPolicy#DISCHARGE}); a helper closed for the backend instead would bring the body
 * of each operation it calls into that tree, and a reader cannot put the operation back.
 *
 * <p>Through a module in the middle, because that module closes what it publishes against its own
 * table, and its table holds what it imported closed the same way or not at all.
 */
class AnImportIsClosedUnderThePolicyItsReaderExpandsInTest {

    private static final String BOTTOM = """
            module chain.bottom exposing ( tailSum )

            let tailSum (values: List<Int>): Int = List.sum(List.drop(1, values))
            """;

    private static final String MIDDLE = """
            module chain.middle exposing ( tailPlus )

            import chain.bottom ( tailSum )

            let tailPlus (values: List<Int>): Int = tailSum(values) + 1
            """;

    private static final String TOP = """
            module chain.top

            import chain.middle ( tailPlus )

            behavior calculate : (values: List<Int>) -> Int
            let calculate (values) = tailPlus(values)
            """;

    private static Db db() {
        return Compilation.ofDocuments(
                Map.of("bottom.sou", BOTTOM, "middle.sou", MIDDLE, "top.sou", TOP),
                Set.of(), ModulePath.EMPTY).db();
    }

    private static ClosedImports importedBy(Db db, String module, InliningPolicy policy) {
        Answer<ClosedImports> imported = db.ask(new Bodies.ImportedDefinitions(module, policy));
        assertTrue(imported.present(), () -> "imports of " + module + ": " + imported.reports());
        return imported.value();
    }

    @Test
    void anOperationTheBottomCallsStillStandsTwoImportsUp() {
        ClosedImports imported = importedBy(db(), "chain.top", InliningPolicy.DISCHARGE);

        assertEquals(InliningPolicy.DISCHARGE, imported.policy());
        Set<String> operations = operationsNamedIn(imported);
        assertTrue(operations.contains("List.drop"), () -> "standing: " + operations);
        assertTrue(operations.contains("List.sum"), () -> "standing: " + operations);
    }

    /** The control: the backend's closing does resolve the operation, so the case above is the
     * policy's doing and not a body that never named it. */
    @Test
    void theBackendsClosingOfTheSameImportHasNoOperationLeftToCall() {
        ClosedImports imported = importedBy(db(), "chain.top", InliningPolicy.FULL);

        Set<String> operations = operationsNamedIn(imported);
        assertFalse(operations.contains("List.drop"), () -> "standing: " + operations);
        assertFalse(imported.definitions().isEmpty(), "the import arrived");
    }

    /** And the table refuses a closing of the other policy, rather than holding the two
     * representations side by side. */
    @Test
    void aTableRefusesImportsClosedUnderAnotherPolicy() {
        Db db = db();
        Hir.Module top = db.ask(new Bodies.Settled("chain.top")).value();
        ClosedImports forTheBackend = importedBy(db, "chain.top", InliningPolicy.FULL);

        assertThrows(IllegalArgumentException.class, () -> HelperTable.of(top, forTheBackend,
                InliningPolicy.DISCHARGE, DefaultStdlib.get()));
    }

    /** Every operation of the language a call in one of {@code imported}'s bodies still names. */
    private static Set<String> operationsNamedIn(ClosedImports imported) {
        Set<String> out = new LinkedHashSet<>();
        for (Hir.FnDef each : imported.definitions().values()) {
            operationsNamedIn(each.writtenBody(), out);
        }
        return out;
    }

    private static void operationsNamedIn(Hir.Expr e, Set<String> out) {
        if (e instanceof Hir.Var.Denoting named
                && named.reachesADeclaration() instanceof ReachName.OfLibrary operation) {
            out.add(operation.rendered());
        }
        Hir.forEachChild(e, c -> operationsNamedIn(c, out));
    }
}
