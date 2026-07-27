package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.meta.ModulePath;

import souther.runtime.ConstraintViolation;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A module compiled by one project is imported by another, from its classes alone. What that module
 * declared is read off the classes the first project built; the second neither has its {@code .sou}
 * nor re-emits anything of it, and a value of its type is built through the very invariant check the
 * first project compiled.
 */
class CrossProjectImportTest {

    private static final String LIBRARY = """
            module shared.money exposing ( Amount )
            data Amount = Int
                invariant value >= 0
            """;

    /** The library project's build: its own compile, and nothing of the consumer's. */
    private static ModulePath published(String... sources) {
        Map<String, byte[]> classes = sources.length == 1
                ? Compiler.compile(sources[0])
                : Compiler.compileModules(List.of(sources));
        return classes::get;
    }

    @Test
    void aModuleOnThePathCanBeImported() {
        Map<String, byte[]> app = Compiler.compileModules(List.of("""
                module app.order
                import shared.money ( Amount )
                data Order = { total: Amount }
                behavior place : (a: Amount) -> Order constructs Order
                let place (a) = Order { total = a }
                """), published(LIBRARY));

        assertTrue(app.containsKey("app.order.Order"));
        assertFalse(app.containsKey("shared.money.Amount"),
                "the dependency's classes are its own build's; this one does not emit them again");
    }

    /** The invariant is enforced across the boundary by the code the library shipped: the consumer
     * calls `__construct`, which is where the check lives. */
    @Test
    void constructingAnImportedTypeRunsTheInvariantTheLibraryCompiled() throws Exception {
        ModulePath path = published(LIBRARY);
        Map<String, byte[]> app = Compiler.compileModules(List.of("""
                module app.order exposing ( Req, place )
                import shared.money ( Amount )
                data Req = { n: Int }
                behavior place : (r: Req) -> Amount constructs Amount
                let place (r) = Amount(r.n)
                """), path);

        Map<String, byte[]> both = new LinkedHashMap<>(app);
        both.put("shared.money.Amount", path.bytes("shared.money.Amount"));
        both.put("shared.money.Amount$Ctfe", path.bytes("shared.money.Amount$Ctfe"));
        BytesClassLoader loader = new BytesClassLoader(both, getClass().getClassLoader());
        Object impl = loader.loadClass("app.order.Place$Impl").getDeclaredConstructor().newInstance();

        Object ok = Codecs.apply(impl, Codecs.decoded(loader, "app.order.Req", Map.of("n", 5L)));
        assertEquals(5L, ok.getClass().getMethod("value").invoke(ok));

        Object bad = Codecs.decoded(loader, "app.order.Req", Map.of("n", -1L));
        assertThrows(ConstraintViolation.class, () -> Codecs.apply(impl, bad));
    }

    /** A dependency of the dependency is read too — the path is walked, not just its first layer. */
    @Test
    void aModuleReachedThroughAnotherIsReadAsWell() {
        ModulePath path = published(LIBRARY, """
                module shared.billing exposing ( Invoice )
                import shared.money ( Amount )
                data Invoice = { total: Amount }
                """);

        Compiler.compileModules(List.of("""
                module app.ledger
                import shared.billing ( Invoice )
                data Entry = { of: Invoice }
                behavior record : (i: Invoice) -> Entry constructs Entry
                let record (i) = Entry { of = i }
                """), path);
    }

    /** An import naming nothing on the path is still the import that is wrong, reported where it is
     * written. */
    @Test
    void anImportOfSomethingNotOnThePathIsUnknown() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module app.order
                        import shared.money ( Amount )
                        data Order = { total: Amount }
                        """), ModulePath.EMPTY));

        assertTrue(e.getMessage().contains("shared.money"), e.getMessage());
        assertTrue(e.getMessage().contains("unknown module"), e.getMessage());
    }

    /** A qualified behavior reference needs no import line, so it can be the only place a dependency
     * is named. The module still has to be read for the reference to bind. */
    @Test
    void aBehaviorNamedThroughItsModuleReadsThatModuleToo() {
        ModulePath path = published("""
                module shared.pricing exposing ( Cart, Priced, quote )
                data Cart = { n: Int }
                data Priced = { total: Int }
                behavior quote : (c: Cart) -> Priced constructs Priced
                let quote (c) = Priced { total = c.n }
                """);

        Compiler.compileModules(List.of("""
                module app.checkout exposing ( Done, place, checkout : Done )
                data Done = { total: Int }
                behavior place : (p: shared.pricing.Priced) -> Done constructs Done
                let place (p) = Done { total = p.total }
                behavior checkout = shared.pricing.quote >-> place
                """), path);
    }

    /** A module on the path needs another that is not there. The import is written in a file this
     * project does not have, so what is reported is the path, naming both modules. */
    @Test
    void aDependencyOfADependencyThatIsAbsentNamesBothModules() {
        Map<String, byte[]> both = Compiler.compileModules(List.of(LIBRARY, """
                module shared.billing exposing ( Invoice )
                import shared.money ( Amount )
                data Invoice = { total: Amount }
                """));
        ModulePath halfThere = name -> name.startsWith("shared.billing") ? both.get(name) : null;

        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module app.ledger
                        import shared.billing ( Invoice )
                        data Entry = { of: Invoice }
                        """), halfThere));

        assertTrue(e.getMessage().contains("shared.billing"), e.getMessage());
        assertTrue(e.getMessage().contains("shared.money"), e.getMessage());
    }

    /** A module compiled here that is also on the path is refused: which one an import means would
     * be settled by nothing the author wrote. */
    @Test
    void aModuleCompiledHereMayNotAlsoBeOnThePath() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module shared.money exposing ( Amount )
                        data Amount = String
                        """, """
                        module app.order
                        import shared.money ( Amount )
                        data Order = { total: Amount }
                        """), published(LIBRARY)));

        assertTrue(e.getMessage().contains("shared.money"), e.getMessage());
    }

    /** What the dependency keeps to itself stays kept: `exposing` is the gate on the far side of a
     * jar exactly as it is within one compile. */
    @Test
    void aTypeTheDependencyDoesNotExposeCannotBeImported() {
        ModulePath path = published("""
                module shared.money exposing ( Amount )
                data Amount = Int
                data Ledger = { balance: Amount }
                """);

        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module app.order
                        import shared.money ( Ledger )
                        data Order = { l: Ledger }
                        """), path));

        assertTrue(e.getMessage().contains("Ledger"), e.getMessage());
    }

    /** An example in the consumer runs against the dependency's real classes, off the same path its
     * declarations were read from. */
    @Test
    void anExampleRunsAgainstTheDependencysOwnClasses() {
        Compiler.compileModules(List.of("""
                module app.order exposing ( Order, place )
                import shared.money ( Amount )
                data Order = { total: Amount }
                behavior place : (a: Amount) -> Order constructs Order
                let place (a) = Order { total = a }
                example place
                    | "an amount becomes an order" : (Amount(5)) -> Order { total = Amount(5) }
                """), published(LIBRARY));
    }
}
