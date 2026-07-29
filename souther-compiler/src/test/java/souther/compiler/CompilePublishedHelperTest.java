package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Modifier;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A module publishes its helpers. A rule written once is then shared: before this, a module that
 * wanted another's pure calculation restated it or declared it a behavior, and a behavior is a
 * business operation whose list stays one-to-one with the specification's (issue #197, ADR-0005).
 *
 * <p>What crosses is the helper closed, as a published value does. The one thing closing cannot
 * remove is a recursive helper, which is a method rather than an expression: those travel with it,
 * named by the module that declares them, and the reader emits them on its own {@code $Fns} — which
 * is what keeps that class package-private and adds no way to reach a construction from Java.
 */
class CompilePublishedHelperTest {

    private static final String PRICING = """
            module pricing exposing ( Amount, taxed )

            data Amount = Int
            data Rate = Int

            let rate = Rate(10)
            let taxed (a: Amount) = Amount(a.value + a.value * rate.value / 100)
            """;

    /**
     * The helper is called, and the reader writes nothing else about it: `Rate` is `pricing`'s and is
     * not named here, and neither is the `Amount` the helper builds declared in `constructs` —
     * publishing `taxed` is what states that origination, and it was stated in `pricing`.
     */
    @Test
    void aHelperIsPublishedAndCalledInAnotherModule() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(PRICING, """
                module order exposing ( Receipt, bill )

                import pricing ( Amount, taxed )

                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt constructs Receipt
                let bill (a) = Receipt { total = taxed(a) }
                """)));
    }

    /** And declaring it anyway is not called building nothing: the construction is there, it is just
     * not this behavior's to state. */
    @Test
    void declaringACarriedConstructionIsNotOverDeclaration() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(PRICING, """
                module order exposing ( Receipt, bill )

                import pricing ( Amount, taxed )

                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt constructs Receipt, Amount
                let bill (a) = Receipt { total = taxed(a) }
                """)));
    }

    /** A type of a third module is neither the reader's nor the publisher's to hand over, so it stays
     * the reader's to declare — which it can, because the module that declares it exposed it. */
    @Test
    void aThirdModulesTypeStaysTheReadersToDeclare() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module money exposing ( Yen )

                        data Yen = Int
                        """, """
                        module pricing exposing ( priced )

                        import money ( Yen )

                        let priced (n: Int) = Yen(n)
                        """, """
                        module order exposing ( Receipt, bill )

                        import money ( Yen )
                        import pricing ( priced )

                        data Receipt = { total: Yen }

                        behavior bill : (n: Int) -> Receipt constructs Receipt
                        let bill (n) = Receipt { total = priced(n) }
                        """)));

        assertTrue(e.getMessage().contains("Yen"), e.getMessage());
    }

    @Test
    void aPublishedRecursiveHelperIsCalledAcrossModules() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module maths exposing ( sumDown )

                partial let sumDown (n: Int) : Int = if n == 0 then 0 else n + sumDown(n - 1)
                """, """
                module order exposing ( Out, bill )

                import maths ( sumDown )

                data Out = { v: Int }

                behavior bill : (n: Int) -> Out constructs Out
                let bill (n) = Out { v = sumDown(n) }
                """)));
    }

    /** A published non-recursive helper that calls a recursive one the module keeps to itself: the
     * private helper is never imported, and arrives because the body that calls it did. */
    @Test
    void anUnimportedRecursiveHelperArrivesWithTheBodyThatCallsIt() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module maths exposing ( total )

                partial let loop (n: Int) : Int = if n == 0 then 0 else n + loop(n - 1)

                let total (n: Int) = loop(n) * 2
                """, """
                module order exposing ( Out, bill )

                import maths ( total )

                data Out = { v: Int }

                behavior bill : (n: Int) -> Out constructs Out
                let bill (n) = Out { v = total(n) }
                """)));
    }

    /** A mutually-recursive group arrives whole: each member is reached from the others, so following
     * the calls collects all of them. */
    @Test
    void aMutuallyRecursiveGroupArrivesWhole() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module maths exposing ( classify )

                partial let even (n: Int) : Int = if n == 0 then 1 else odd(n - 1)
                partial let odd (n: Int) : Int = if n == 0 then 0 else even(n - 1)

                let classify (n: Int) = even(n)
                """, """
                module order exposing ( Out, bill )

                import maths ( classify )

                data Out = { v: Int }

                behavior bill : (n: Int) -> Out constructs Out
                let bill (n) = Out { v = classify(n) }
                """)));
    }

    /** A published helper may call one another module published to it, and the module at the end of
     * the chain imports only its neighbour. Closing a body therefore reads everything the declaring
     * module can name, not only what it declares. */
    @Test
    void aPublishedHelperMayCallOneAnotherModulePublished() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module low exposing ( doubled )

                let doubled (n: Int) = n * 2
                """, """
                module mid exposing ( quadrupled )

                import low ( doubled )

                let quadrupled (n: Int) = doubled(doubled(n))
                """, """
                module top exposing ( Out, bill )

                import mid ( quadrupled )

                data Out = { v: Int }

                behavior bill : (n: Int) -> Out constructs Out
                let bill (n) = Out { v = quadrupled(n) }
                """)));
    }

    /** The same chain with a recursive helper two modules up: it is passed along as the module that
     * declares it closed it, and the module at the end emits the method. */
    @Test
    void aRecursiveHelperTwoModulesUpArrivesThroughTheChain() throws Exception {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module low exposing ( summed )

                partial let summed (n: Int) : Int = if n == 0 then 0 else n + summed(n - 1)
                """, """
                module mid exposing ( twiceSummed )

                import low ( summed )

                let twiceSummed (n: Int) = summed(n) * 2
                """, """
                module top exposing ( Out, bill )

                import mid ( twiceSummed )

                data Out = { v: Int }

                behavior bill : (n: Int) -> Out constructs Out
                let bill (n) = Out { v = twiceSummed(n) }
                """));

        Class<?> fns = new BytesClassLoader(classes, getClass().getClassLoader())
                .loadClass("top.$Fns");
        assertEquals(List.of("low$summed"), java.util.Arrays.stream(fns.getDeclaredMethods())
                .map(java.lang.reflect.Method::getName).sorted().toList());
    }

    /** A helper folds, and folding reaches `List.foldFrom`, the one recursive prelude helper. The
     * reader emits it whether or not it folds itself — which it is found to need by following the
     * calls of what it imported, not by reading its own bodies. */
    @Test
    void aPublishedHelperThatFoldsIsCalledByAReaderThatDoesNot() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module maths exposing ( total )

                let total (xs: List<Int>) = List.fold((acc, x) -> acc + x, 0, xs)
                """, """
                module order exposing ( Out, bill )

                import maths ( total )

                data Out = { v: Int }

                behavior bill : (xs: List<Int>) -> Out constructs Out
                let bill (xs) = Out { v = total(xs) }
                """)));
    }

    /**
     * Two modules declaring a recursive helper of one name are two helpers, and one reader may end up
     * emitting both: it imports {@code up.a}'s by name and receives {@code up.b}'s because the body it
     * imported from there calls it. A bare name could not tell them apart, so the method each becomes
     * is named by the module that declares it.
     */
    @Test
    void twoModulesRecursiveHelpersOfOneNameStayTwoMethods() throws Exception {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module up.a exposing ( step )

                partial let step (n: Int) : Int = if n == 0 then 1 else step(n - 1)
                """, """
                module up.b exposing ( viaStep )

                partial let step (n: Int) : Int = if n == 0 then 2 else step(n - 1)

                let viaStep (n: Int) = step(n) * 10
                """, """
                module order exposing ( Out, bill )

                import up.a ( step )
                import up.b ( viaStep )

                data Out = { v: Int }

                behavior bill : (n: Int) -> Out constructs Out
                let bill (n) = Out { v = step(n) + viaStep(n) }
                """));

        assertTrue(classes.containsKey("order.$Fns"), classes.keySet().toString());
        Class<?> fns = new BytesClassLoader(classes, getClass().getClassLoader())
                .loadClass("order.$Fns");
        List<String> methods = java.util.Arrays.stream(fns.getDeclaredMethods())
                .map(java.lang.reflect.Method::getName).sorted().toList();
        assertEquals(List.of("up$a$step", "up$b$step"), methods);
    }

    /** The method goes on the compiling module's own `$Fns`, which stays package-private. A helper's
     * declaring module is its identity, not where its method lives — so publishing one opens no
     * Java-reachable entry, and a construction inside it is no more reachable than before. */
    @Test
    void aCarriedHelperIsEmittedOnThePackagePrivateFnsOfTheReader() throws Exception {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module maths exposing ( built )

                data Wrapped = Int

                partial let loop (n: Int) : Wrapped = if n == 0 then Wrapped(0) else loop(n - 1)
                """.replace("exposing ( built )", "exposing ( Wrapped, loop )"), """
                module order exposing ( Out, bill )

                import maths ( Wrapped, loop )

                data Out = { v: Int }

                behavior bill : (n: Int) -> Out constructs Out
                let bill (n) = Out { v = loop(n).value }
                """));

        assertTrue(classes.containsKey("order.$Fns"), classes.keySet().toString());
        Class<?> fns = new BytesClassLoader(classes, getClass().getClassLoader())
                .loadClass("order.$Fns");
        assertFalse(Modifier.isPublic(fns.getModifiers()), "$Fns is package-private");
        for (java.lang.reflect.Method m : fns.getDeclaredMethods()) {
            assertFalse(Modifier.isPublic(m.getModifiers()),
                    m.getName() + " is reachable from another package");
        }
    }

    /** A published helper crosses a project boundary too: the jar carries the helper and what its
     * body reaches, and the importing project closes and expands it the same way. */
    @Test
    void aHelperCrossesAProjectBoundary() throws Exception {
        Map<String, byte[]> classes = Compiler.compile(PRICING);
        ModulePath path = classes::get;

        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module app.billing exposing ( Receipt, bill )

                import pricing ( Amount, taxed )

                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt constructs Receipt
                let bill (a) = Receipt { total = taxed(a) }
                """), path));
    }

    /** A reader has to write the arguments, so it has to be able to name their types. */
    @Test
    void aPublishedHelperMayNotTakeATypeTheModuleKeepsToItself() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( applied )

                data Hidden = Int

                let applied (h: Hidden) = h.value + 1
                """));

        assertTrue(e.getMessage().contains("Hidden"), e.getMessage());
    }

    @Test
    void aPublishedHelperMayNotReturnATypeTheModuleKeepsToItself() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( wrapped )

                data Hidden = Int

                let wrapped (n: Int) = Hidden(n)
                """));

        assertTrue(e.getMessage().contains("Hidden"), e.getMessage());
    }

    /** The same for a recursive one, read off the return type it is required to declare. */
    @Test
    void aPublishedRecursiveHelperMayNotReturnATypeTheModuleKeepsToItself() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( wrapped )

                data Hidden = Int

                partial let wrapped (n: Int) : Hidden =
                    if n == 0 then Hidden(0) else wrapped(n - 1)
                """));

        assertTrue(e.getMessage().contains("Hidden"), e.getMessage());
    }

    /** A helper a module keeps to itself is not reachable, as any unexposed name is. */
    @Test
    void anUnpublishedHelperHasNoNameInAReader() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module pricing exposing ( Amount )

                        data Amount = Int

                        let taxed (a: Amount) = Amount(a.value * 2)
                        """, """
                        module order exposing ( Receipt, bill )

                        import pricing ( Amount, taxed )

                        data Receipt = { total: Amount }

                        behavior bill : (a: Amount) -> Receipt constructs Receipt
                        let bill (a) = Receipt { total = taxed(a) }
                        """)));

        assertTrue(e.getMessage().contains("taxed"), e.getMessage());
    }

    /** A module that publishes nothing recursive emits no `$Fns` at all — the class appears because
     * a method has to go somewhere, not because a helper was imported. */
    @Test
    void aReaderOfANonRecursiveHelperEmitsNoFnsClass() throws Exception {
        Map<String, byte[]> classes = Compiler.compileModules(List.of(PRICING, """
                module order exposing ( Receipt, bill )

                import pricing ( Amount, taxed )

                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt constructs Receipt
                let bill (a) = Receipt { total = taxed(a) }
                """));

        assertFalse(classes.containsKey("order.$Fns"), classes.keySet().toString());
        assertEquals(0, classes.keySet().stream().filter(n -> n.endsWith("$Fns")).count(),
                classes.keySet().toString());
    }
}
