package souther.compiler.frontend;

import souther.compiler.ast.Ast;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A module's declarations can be taken back out of the source it was parsed from, each under the
 * name it declares. This is how a module publishes what it declares: the text goes into the jar and
 * the importing project parses it back, rather than reading a second description of the same syntax.
 */
class CstSlicesTest {

    @Test
    void everyDeclarationOfARealModuleIsAccountedFor() throws IOException {
        String source = Files.readString(Path.of("../examples/ordering/src/main/souther/cart.sou"));

        CstFrontend.Parsed parsed = CstFrontend.parseWithSlices(source, null);

        Ast.Module module = parsed.module();
        CstFrontend.Slices slices = parsed.slices();
        assertEquals(module.imports().size(), slices.imports().size());
        assertEquals(module.defs().size(), slices.defs().size());
        assertEquals(module.behaviors().size(), slices.behaviors().size());
        assertEquals(module.fns().size(), slices.fns().size());
        for (Ast.Def def : module.defs()) {
            assertTrue(slices.defs().get(def.name()).contains("data " + def.name()),
                    slices.defs().get(def.name()));
        }
    }

    @Test
    void aDeclarationComesBackAsItWasWritten() {
        CstFrontend.Slices slices = CstFrontend.parseWithSlices("""
                module shared.money exposing ( Amount )
                import String ( length )

                // what a payment is worth
                data Amount = Int
                    invariant value >= 0

                behavior charge : (a: Amount) -> Amount constructs Amount
                let charge (a) = a
                """, null).slices();

        assertEquals("import String ( length )", slices.imports().get(0));
        assertEquals("""
                // what a payment is worth
                data Amount = Int
                    invariant value >= 0""", slices.defs().get("Amount"));
        assertEquals("behavior charge : (a: Amount) -> Amount constructs Amount",
                slices.behaviors().get("charge"));
        assertEquals("let charge (a) = a", slices.fns().get("charge"));
    }
}
