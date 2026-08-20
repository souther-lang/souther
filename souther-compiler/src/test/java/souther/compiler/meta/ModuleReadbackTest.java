package souther.compiler.meta;

import souther.compiler.Compiler;
import souther.compiler.ast.Ast;
import souther.compiler.codegen.Backend;
import souther.compiler.frontend.CstFrontend;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a module publishes into its classes comes back as the module another project needs in order
 * to import it: the same declarations, read by the same front end. Its implementation does not come
 * back, and is not needed — only the helpers an invariant calls, which are part of what a type is.
 */
class ModuleReadbackTest {

    private static ReadableModule readBack(String moduleName, Map<String, byte[]> classes) {
        return assertInstanceOf(ReadableModule.class, assertInstanceOf(Readback.Ready.class,
                ModuleReadback.read(moduleName, new ClassFileDeclarations(classes::get))).value());
    }

    /** Why a readback would not answer, as the arm rather than as a message it was raised with. */
    private static Readback.Failure refusalOf(String moduleName, PublishedClasses classes) {
        return assertInstanceOf(Readback.NotReady.Unreadable.class,
                ModuleReadback.read(moduleName, classes)).why();
    }

    @Test
    void theDeclarationsComeBackAndTheImplementationDoesNot() {
        String source = """
                module shared.money exposing ( Amount, Receipt, charge )
                import String ( length )

                data Amount = Int
                    invariant value >= 0 && withinCap(value)

                data Receipt = { paid: Amount }
                data Declined

                behavior charge : (a: Amount) -> Receipt | Declined
                    constructs Receipt
                let charge (a) = if a.value > 0 then Receipt { paid = a } else Declined

                let withinCap (n: Int) = n <= 1000000
                let unrelated (n: Int) = n + 1
                """;
        Ast.Module written = CstFrontend.parse(source, null);

        ReadableModule read = readBack("shared.money", Compiler.compile(source));

        Ast.Module back = read.module();
        assertEquals(written.name(), back.name());
        assertEquals(written.exposing(), back.exposing());
        assertEquals(names(written.defs()), names(back.defs()));
        assertEquals(List.of("charge"), back.behaviors().stream().map(Ast.BehaviorDef::name).toList());
        // the invariant needs `withinCap`, so it came; `charge` and `unrelated` are implementation
        assertEquals(List.of("withinCap"), back.fns().stream().map(Ast.FnDef::name).toList());
    }

    /** The declaration is the same declaration, invariant and all — that is what the discharge
     * analysis reads on the importing side. */
    @Test
    void anImportedTypeArrivesWithItsInvariant() {
        ReadableModule read = readBack("shared.money", Compiler.compile("""
                module shared.money exposing ( Amount )
                data Amount = Int
                    invariant value >= 0
                """));

        Ast.Data amount = (Ast.Data) read.module().defs().get(0);
        assertTrue(amount.newtype());
        assertFalse(amount.invariants().isEmpty(), "the invariant did not come back");
    }

    /** An import comes back when a declaration names what it brings in, and not otherwise: the
     * `let` that needed the other one is not part of what was published. */
    @Test
    void onlyTheImportsTheDeclarationsNameComeBack() {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module shared.money exposing ( Amount )
                data Amount = Int
                """, """
                module shared.audit exposing ( Trail )
                data Trail = String
                """, """
                module shared.billing exposing ( Invoice )
                import shared.money ( Amount )
                import shared.audit ( Trail )
                data Invoice = { total: Amount }
                let describe (t: Trail) = t
                """));

        ReadableModule read = readBack("shared.billing", classes);

        assertEquals(List.of("shared.money"),
                read.module().imports().stream().map(Ast.Import::module).toList());
    }

    /** No `let` comes back for any behavior, so which ones are injection targets cannot be read off
     * the module; it is carried beside it. */
    @Test
    void whichBehaviorsAreInjectedIsCarried() {
        ReadableModule read = readBack("shared.ledger", Compiler.compile("""
                module shared.ledger exposing ( Entry, record, double )
                data Entry = { amount: Int }
                behavior record : (e: Entry) -> Entry
                behavior double : (e: Entry) -> Entry constructs Entry
                let double (e) = Entry { amount = e.amount * 2 }
                """));

        assertEquals(Set.of("record"), read.injectedBehaviors());
    }

    /** A composition declares stages; what comes back is the signature it computes to, with every
     * name written out, because nothing is known here about what the reading module imports. */
    @Test
    void aCompositionComesBackAsASignature() {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module shop.pricing exposing ( Cart, Priced, quote )
                data Cart = { n: Int }
                data Priced = { total: Int }
                behavior quote : (c: Cart) -> Priced constructs Priced
                let quote (c) = Priced { total = c.n }
                """, """
                module shop.checkout exposing ( Done, place, checkout : Done )
                import shop.pricing ( Cart, Priced, quote )
                data Done = { total: Int }
                behavior place : (p: Priced) -> Done constructs Done
                let place (p) = Done { total = p.total }
                behavior checkout = quote >-> place
                """));

        ReadableModule read = readBack("shop.checkout", classes);

        Ast.SpecBehavior checkout = (Ast.SpecBehavior) read.module().behaviors().stream()
                .filter(b -> b.name().equals("checkout")).findFirst().orElseThrow();
        assertEquals("shop.pricing.Cart", refName(checkout.params().get(0).type()));
        assertEquals("shop.checkout.Done", refName(checkout.ret()));
    }

    /** The name of a written type's single reference case. */
    private static String refName(Ast.RetType ret) {
        return ((Ast.TypeRef) ret.cases().get(0)).name();
    }

    /** Every module of a real, layered module set survives the round trip. */
    @Test
    void everyModuleOfALayeredSetComesBack() {
        String base = """
                module shop.base exposing ( Money, Sku )
                import String ( length )
                data Money = Int
                    invariant value >= 0
                data Sku = String
                    invariant length(value) >= 1
                """;
        String catalog = """
                module shop.catalog exposing ( Item, Priced, Missing, price )
                import shop.base ( Money, Sku )
                data Item = { sku: Sku, unit: Money, count: Int }
                data Priced = { amount: Money }
                data Missing
                behavior price : (i: Item) -> Priced | Missing constructs Priced
                let price (i) = if i.count >= 1 then Priced { amount = i.unit } else Missing
                """;
        String order = """
                module shop.order exposing ( Line, Total, sum )
                import shop.catalog ( Item )
                import shop.base ( Money )
                data Line = { item: Item, count: Int }
                data Total = { amount: Money }
                behavior sum : (l: Line) -> Total constructs Total, Money
                let sum (l) = Total { amount = Money(l.item.unit.value * l.count) }
                """;
        Map<String, byte[]> classes = Compiler.compileModules(List.of(base, catalog, order));

        for (String name : List.of("shop.base", "shop.catalog", "shop.order")) {
            ReadableModule read = readBack(name, classes);
            assertEquals(name, read.module().name(), name + " did not come back");
        }
        assertEquals(names(CstFrontend.parse(order, null).defs()),
                names(readBack("shop.order", classes).module().defs()));
    }

    /** An invariant can name a helper without calling it — handing it to a combinator is the usual
     * way — and the helper is no less needed for being named that way. */
    @Test
    void aHelperAnInvariantHandsToACombinatorComesToo() {
        ReadableModule read = readBack("shop.basket", Compiler.compile("""
                module shop.basket exposing ( Basket )
                import List ( all )
                data Basket = { items: List<Int> }
                    invariant all(positive, items)
                let positive (n: Int) = n >= 1
                """));

        assertEquals(List.of("positive"),
                read.module().fns().stream().map(Ast.FnDef::name).toList());
    }

    /**
     * Carrying nothing for a name is its own answer, told apart from carrying something unreadable.
     *
     * <p>The two settle different questions. An import of a name these classes say nothing about is
     * an import of a module nobody has; an import of one they carry and this compiler will not read
     * reaches a module that is there, and an author told there is no such thing would be told
     * something false about their own dependency list.
     */
    @Test
    void aNameThatIsNotACompiledModuleReadsAsNothing() {
        assertInstanceOf(Readback.NotReady.SaysNothing.class,
                ModuleReadback.read("shared.money", new ClassFileDeclarations(Map.<String,
                        byte[]>of()::get)));
    }

    /** A module built against a boundary this compiler does not share is refused, rather than read
     * and misunderstood. */
    @Test
    void aModuleFromADifferentBoundaryIsRefused() {
        Map<String, byte[]> classes = Compiler.compile("""
                module shared.money exposing ( Amount )
                data Amount = Int
                """);
        PublishedClasses stale = viewing(classes, m -> new PublishedClasses.SoutherModuleView(
                m.compat() + 1, "0.0.1-old", m.header(), m.imports(), m.types(),
                m.behaviors(), m.invariantHelpers()));

        Readback.Failure.Incompatible why = assertInstanceOf(
                Readback.Failure.Incompatible.class, refusalOf("shared.money", stale));

        assertEquals("0.0.1-old", why.compiler());
    }

    /**
     * And an older one, which is the direction the termination guarantee depends on. A helper written
     * without {@code partial} promises that nothing it reaches is {@code partial} (spec §fn-rules), and
     * a reader answers off that word instead of walking the closure behind it. A jar built before the
     * rule carries unmarked helpers that were never held to it, so it is refused rather than believed.
     */
    @Test
    void aModuleFromAnEarlierBoundaryIsRefusedToo() {
        Map<String, byte[]> classes = Compiler.compile("""
                module shared.money exposing ( Amount, taxed )
                data Amount = Int
                let taxed (a: Amount) = Amount(a.value * 110 / 100)
                """);
        PublishedClasses older = viewing(classes, m -> new PublishedClasses.SoutherModuleView(
                m.compat() - 1, "0.0.1-older", m.header(), m.imports(), m.types(),
                m.behaviors(), m.invariantHelpers()));

        Readback.Failure.Incompatible why = assertInstanceOf(
                Readback.Failure.Incompatible.class, refusalOf("shared.money", older));

        assertEquals("0.0.1-older", why.compiler());
    }

    /** A published helper's body travels as source and is compiled by whoever imports it, so what
     * that source means is part of the same boundary. A jar that disagrees is refused as a version
     * disagreement, rather than read and reported as an unresolved name inside a body nobody wrote. */
    @Test
    void aModuleCarryingAPublishedHelperIsRefusedAtADifferentBoundary() {
        Map<String, byte[]> classes = Compiler.compile("""
                module shared.money exposing ( Amount, taxed )
                data Amount = Int
                let taxed (a: Amount) = Amount(a.value * 110 / 100)
                """);
        assertEquals(List.of("taxed"),
                readBack("shared.money", classes).module().fns().stream()
                        .map(Ast.FnDef::name).toList());

        PublishedClasses stale = viewing(classes, m -> new PublishedClasses.SoutherModuleView(
                m.compat() + 1, "0.0.1-old", m.header(), m.imports(), m.types(),
                m.behaviors(), m.invariantHelpers()));

        Readback.Failure.Incompatible why = assertInstanceOf(
                Readback.Failure.Incompatible.class, refusalOf("shared.money", stale));

        assertEquals("0.0.1-old", why.compiler());
    }

    /**
     * A reading answers about the module it was asked for, or it does not answer.
     *
     * <p>What is asked for and what comes back are two names, and nothing held them together: the
     * class is found by the name the caller asked about, and the module is named by the header that
     * class carries. An artifact whose header names something else came back {@code Ready}, and what
     * the walk over the path then held was a module filed under a name that is not its own — every
     * question about it answered from the wrong module, and no report anywhere saying so.
     *
     * <p>Not reachable through a jar this compiler agrees with: the declaring project's own build
     * names the class after the module. It is reachable through one it does not agree with, which is
     * the case this reading exists to be clear about.
     */
    @Test
    void oneWhoseHeaderNamesAnotherModuleIsNotTheModuleThatWasAskedFor() {
        Map<String, byte[]> classes = Compiler.compile("""
                module shared.money exposing ( Amount )
                data Amount = Int
                """);
        PublishedClasses renamed = viewing(classes, m -> new PublishedClasses.SoutherModuleView(
                m.compat(), m.compiler(), "module shared.other exposing ( Amount )",
                m.imports(), m.types(), m.behaviors(), m.invariantHelpers()));

        Readback.Failure.AnotherModule why = assertInstanceOf(
                Readback.Failure.AnotherModule.class, refusalOf("shared.money", renamed));

        assertEquals("shared.other", why.named(),
                "the name the artifact gave itself, which is not the one it was filed under");
    }

    /**
     * Every declaration the indexing refused crosses, and not only the first.
     *
     * <p>The indexing reads the whole module and answers with every refusal it saw, so keeping one
     * would be this boundary deciding to lose the others — a rule about what an artifact is, made
     * where an artifact is being described. What is shown to an author is one sentence, and that is
     * a question about a report rather than about the facts a report is written from.
     */
    @Test
    void everyDeclarationItRefusesCrosses() {
        Map<String, PublishedClasses.Declarations> published = Map.of(
                "lib.two.$Module", new PublishedClasses.Declarations(
                        new PublishedClasses.SoutherModuleView(Backend.BOUNDARY_VERSION,
                                "another build", "module lib.two exposing ( Held )", List.of(),
                                List.of("Held", "Twice", "Some"), List.of(), List.of()),
                        null, null, null),
                "lib.two.Held", declaring("data Held = String"),
                "lib.two.Twice", declaring("data Held = Int"),
                "lib.two.Some", declaring("data Some = String"));

        Readback.Failure why =
                refusalOf("lib.two", name -> PublishedClasses.carrying(published.get(name)));

        Readback.Failure.InvalidDeclarations refused =
                assertInstanceOf(Readback.Failure.InvalidDeclarations.class, why);
        assertEquals(new Readback.DeclarationRejection.DeclaredTwice("Held"), refused.first());
        assertEquals(List.of(new Readback.DeclarationRejection.BuiltInOptionCaseDeclared("Some")),
                refused.rest(), "the rest of what the indexing saw, in the order it saw them");
    }

    /** The class one declaration was stamped on. */
    private static PublishedClasses.Declarations declaring(String declaration) {
        return new PublishedClasses.Declarations(null, declaration, null, null);
    }

    /** {@code classes}, with whatever their `$Module` annotation says rewritten by {@code as}. */
    private static PublishedClasses viewing(
            Map<String, byte[]> classes,
            java.util.function.UnaryOperator<PublishedClasses.SoutherModuleView> as) {
        ClassFileDeclarations read = new ClassFileDeclarations(classes::get);
        return binaryName -> {
            if (!(read.of(binaryName)
                    instanceof PublishedClasses.Carried.Declared(
                            PublishedClasses.Declarations d))
                    || d.module() == null) {
                return read.of(binaryName);
            }
            return new PublishedClasses.Carried.Declared(new PublishedClasses.Declarations(
                    as.apply(d.module()), d.data(), d.behaviorSignature(), d.behaviorInjected()));
        };
    }

    private static List<String> names(List<Ast.Def> defs) {
        return defs.stream().map(Ast.Def::name).toList();
    }
}
