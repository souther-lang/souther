package souther.compiler;

import souther.compiler.diag.CompileException;

import net.unit8.raoh.Err;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Result;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** Multi-module compilation with explicit imports and cyclic-import detection (spec 4, 22.11). */
class CompileModuleTest {

    private static final String EMPLOYEE = """
            module example.employee exposing (
                従業員ID
            )

            import String ( length )

            data 従業員ID = String
                invariant length(value) > 0
            """;

    private static final String TRIP = """
            module example.trip exposing (
                Trip
            )

            import example.employee (
                従業員ID
            )

            data Trip = { who: 従業員ID }
            """;

    @Test
    void crossModuleTypeResolvesAndRoundTrips() throws Exception {
        Map<String, byte[]> classes = Compiler.compileModules(List.of(EMPLOYEE, TRIP));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());

        // the imported 従業員ID class lives in the declaring module's package
        loader.loadClass("example.employee.従業員ID");

        Result<?> r = Codecs.decode(loader, "example.trip.Trip", Map.of("who", "e-1"));
        assertTrue(r instanceof Ok);

        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "example.trip.Trip", ((Ok<?>) r).value());
        assertEquals("e-1", out.get("who"));

        // the imported type's invariant still runs during cross-module decode
        assertTrue(Codecs.decode(loader, "example.trip.Trip", Map.of("who", "")) instanceof Err);
    }

    @Test
    void cyclicImportIsE1501() {
        String a = """
                module m.a exposing ( A )
                import m.b ( B )
                data A = { b: B }
                """;
        String b = """
                module m.b exposing ( B )
                import m.a ( A )
                data B = String
                """;
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(a, b)));
        assertEquals("E1501", e.code());
    }

    /** One module on its own has nothing to import from, so the import line is what is wrong. Left
     * to fall through, the name would go missing and the report would land on its first use. */
    @Test
    void anImportInASingleSourceNamesAModuleThatIsNotThere() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module app.order
                import shared.money ( Amount )
                data Order = { total: Amount }
                """));
        assertTrue(e.getMessage().contains("shared.money"), e.getMessage());
        assertTrue(e.getMessage().contains("unknown module"), e.getMessage());
    }

    /** A standard-library import is not a module import: it is stripped before that check. */
    @Test
    void aStandardLibraryImportInASingleSourceStillCompiles() {
        Compiler.compile("""
                module app.order
                import String ( length )
                data Code = String
                    invariant length(value) > 0
                """);
    }
}
