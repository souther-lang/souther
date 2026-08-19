package souther.compiler;

import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeSymbol;
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

    /** A declaration travels as the source that wrote it, so anything the declaration form admits has
     * to survive being written out and read back. A newtype's base is a written type, which since it
     * may be a collection is no longer a single identifier. */
    @Test
    void aCollectionNewtypeSurvivesBeingPublishedAndReadBack() {
        ModulePath path = published("""
                module shared.tagging exposing ( Tags, Stock )
                data Tags = List<String>
                data Stock = Map<String, Int>
                """);

        Map<String, byte[]> app = Compiler.compileModules(List.of("""
                module app.catalog exposing ( Item )
                import List ( length )
                import shared.tagging ( Tags )
                data Item = { tags: Tags, count: Int }

                behavior countTags : (t: Tags) -> Int
                let countTags (t) = {
                    let Tags(xs) = t
                    length(xs)
                }
                """), path);

        assertTrue(app.containsKey("app.catalog.Item"));
        assertFalse(app.containsKey("shared.tagging.Tags"),
                "the dependency's classes are its own build's");
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
        both.put(Emitted.ctfe("shared.money", "Amount"), path.bytes(Emitted.ctfe("shared.money", "Amount")));
        BytesClassLoader loader = new BytesClassLoader(both, getClass().getClassLoader());
        Object impl = Emitted.behavior(loader, "app.order", "place").getDeclaredConstructor().newInstance();

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
        assertTrue(e.getMessage().contains("Unknown module"), e.getMessage());
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

    /** A library's `let` bodies are not published, so an import only they needed is not part of what
     * an importing project reads. Requiring it on the path would make a consumer carry a dependency
     * nothing it can see mentions. */
    @Test
    void anImportOnlyAnUnpublishedLetNeededIsNotRequiredOnThePath() {
        Map<String, byte[]> both = Compiler.compileModules(List.of("""
                module shared.audit exposing ( Trail )
                data Trail = String
                """, """
                module shared.billing exposing ( Invoice )
                import shared.audit ( Trail )
                data Invoice = { total: Int }
                let describe (t: Trail) = t
                """));
        ModulePath billingOnly = name -> name.startsWith("shared.billing") ? both.get(name) : null;

        Compiler.compileModules(List.of("""
                module app.ledger
                import shared.billing ( Invoice )
                data Entry = { of: Invoice }
                behavior record : (i: Invoice) -> Entry constructs Entry
                let record (i) = Entry { of = i }
                """), billingOnly);
    }

    /** A spread names a type without writing it as a field's type, so an import a published
     * declaration needs is not always one a field mentions. It is still needed on the path. */
    @Test
    void anImportOnlySpreadIntoAPublishedDataIsStillRequired() {
        Map<String, byte[]> both = Compiler.compileModules(List.of("""
                module shared.base exposing ( Common )
                data Common = { id: String }
                """, """
                module shared.billing exposing ( Invoice )
                import shared.base ( Common )
                data Invoice = { ...Common, total: Int }
                """));
        ModulePath billingOnly = name -> name.startsWith("shared.billing") ? both.get(name) : null;

        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module app.ledger
                        import shared.billing ( Invoice )
                        data Entry = { of: Invoice }
                        """), billingOnly));

        assertTrue(e.getMessage().contains("shared.billing"), e.getMessage());
        assertTrue(e.getMessage().contains("shared.base"), e.getMessage());
    }

    /** An import that brings in no name is used through its alias alone. The alias is what the
     * declarations write, so that is what says the import is needed. */
    @Test
    void anImportUsedOnlyThroughItsAliasIsStillRequired() {
        Map<String, byte[]> both = Compiler.compileModules(List.of("""
                module shared.audit exposing ( Trail )
                data Trail = String
                """, """
                module shared.billing exposing ( Invoice )
                import shared.audit as A
                data Invoice = { trail: A.Trail }
                """));
        ModulePath billingOnly = name -> name.startsWith("shared.billing") ? both.get(name) : null;

        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module app.ledger
                        import shared.billing ( Invoice )
                        data Entry = { of: Invoice }
                        """), billingOnly));

        assertTrue(e.getMessage().contains("shared.audit"), e.getMessage());
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

    /** A unit the library only named in a sum (spec §unit-data) is one of its declarations like any other,
     * so it is published on its class and read back here — the consumer builds it by name. */
    @Test
    void aUnitOnlyNamedByASumIsPublishedToo() throws Exception {
        ModulePath path = published("""
                module shared.terms exposing ( Terms, Net30 )
                data Terms = Net15 | Net30
                """);

        Map<String, byte[]> app = Compiler.compileModules(List.of("""
                module app.billing
                import shared.terms ( Terms, Net30 )
                data Req = { n: Int }
                behavior pick : (r: Req) -> Terms
                let pick (r) = Net30
                """), path);

        Map<String, byte[]> both = new LinkedHashMap<>(app);
        both.put("shared.terms.Terms", path.bytes("shared.terms.Terms"));
        both.put("shared.terms.Net30", path.bytes("shared.terms.Net30"));
        BytesClassLoader loader = new BytesClassLoader(both, getClass().getClassLoader());
        Object impl = Emitted.behavior(loader, "app.billing", "pick").getDeclaredConstructor().newInstance();

        Object out = Codecs.apply(impl, Codecs.decoded(loader, "app.billing.Req", Map.of("n", 1L)));
        assertEquals("shared.terms.Net30", out.getClass().getName());
    }

    /**
     * The library's type as a member of the consumer's output union. The bridge case is the
     * consumer's own class, so nothing of the library is regenerated — the property that made
     * whole-program union membership unavailable does not arise here (ADR-0057).
     */
    @Test
    void anImportedTypeIsAUnionMemberWithoutTouchingTheLibrary() throws Exception {
        Map<String, byte[]> app = Compiler.compileModules(List.of("""
                module app.billing exposing ( NothingOwed, owed )
                import shared.money ( Amount )
                data NothingOwed
                behavior owed : (a: Amount, b: Amount) -> Amount | NothingOwed
                    constructs Amount
                let owed (a, b) = if a.value >= b.value then Amount(a.value - b.value) else NothingOwed
                """), published(LIBRARY));

        assertTrue(app.containsKey(Emitted.bridgeCase("app.billing", TypeSymbols.declared(new TypeKey("shared.money", "Amount")))),
                "the bridge case is this project's own class");
        assertFalse(app.containsKey("shared.money.Amount"),
                "and the library is not emitted again to carry the interface");
    }
}
