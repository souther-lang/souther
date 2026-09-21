package souther.compiler;

import souther.compiler.diag.msg.ParseMessage;
import souther.compiler.diag.CompileException;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Modifier;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
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

            let rate = 10
            let taxed (a: Amount) =
                Amount(a.value + Rational.toInt(DOWN, a.value * rate / 100))
            """;

    /**
     * The helper is called, and the reader writes nothing else about it: `rate` is `pricing`'s and is
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

    /** A recursive helper is not expanded, so what it builds reaches the caller through its
     * construction set rather than through its body — and it has to reach it as the kind it is, or a
     * reader that declares a carried construction is told it builds nothing. */
    @Test
    void declaringAConstructionCarriedByARecursiveHelperIsNotOverDeclaration() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module pricing exposing ( Amount, make )

                data Amount = Int

                partial let make (n: Int) : Amount =
                    if n == 0 then Amount(0) else make(n - 1)
                """, """
                module order exposing ( Receipt, bill )

                import pricing ( Amount, make )

                data Receipt = { total: Amount }

                behavior bill : (n: Int) -> Receipt constructs Receipt, Amount
                let bill (n) = Receipt { total = make(n) }
                """)));
    }

    /** A unit data is constructed by being named, so a published body that builds one carries that
     * the same way — the reader has no `constructs` to write for a type it cannot name. */
    @Test
    void aUnitDataAPublishedBodyBuildsIsCarriedToo() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module pricing exposing ( Marker, doubled )

                data Marker

                let doubled (n: Int) = if Marker == Marker then n * 2 else n
                """, """
                module order exposing ( Out, bill )

                import pricing ( doubled )

                data Out = { v: Int }

                behavior bill : (n: Int) -> Out constructs Out
                let bill (n) = Out { v = doubled(n) }
                """)));
    }

    /** And it stays the unit it is: a reader declaring one of the same spelling declares a different
     * type, which the carried construction is neither attributed to nor emitted as. */
    @Test
    void aCarriedUnitDataIsNotTheReadersUnitOfThatName() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module pricing exposing ( Marker, doubled )

                data Marker

                let doubled (n: Int) = if Marker == Marker then n * 2 else n
                """, """
                module order exposing ( Marker, Out, bill )

                import pricing ( doubled )

                data Marker
                data Out = { v: Int }

                behavior bill : (n: Int) -> Out constructs Out
                let bill (n) = Out { v = doubled(n) }
                """)));
    }

    /**
     * The reader's own unit data is no more the reader's to declare than a carried one.
     *
     * <p>Where the two above turn on whose construction it is, this one says the question is not
     * asked of a unit at all: it is in no construction set, carried or originated
     * (spec §constructs-excludes-unit-data). Both answers, because a check that had stopped reading
     * the clause would pass the first alone.
     */
    @Test
    void theReadersOwnUnitDataIsNoMoreItsToDeclareThanACarriedOne() {
        String src = """
                module order exposing ( Marker, Out, bill )

                data Marker
                data Out = { v: Int }

                behavior bill : (n: Int) -> Out constructs Out
                let bill (n) = Out { v = if Marker == Marker then n else 0 }
                """;
        assertDoesNotThrow(() -> Compiler.compile(src));

        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(src.replace("constructs Out", "constructs Out, Marker")));
        assertEquals("E1026", e.code());
        assertTrue(e.getMessage().contains("Marker"), e.getMessage());
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

                partial let total (n: Int) = loop(n) * 2
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

                partial let classify (n: Int) = even(n)
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
        Map<String, ClassFileImage> classes = Compiler.compileModules(List.of("""
                module low exposing ( summed )

                partial let summed (n: Int) : Int = if n == 0 then 0 else n + summed(n - 1)
                """, """
                module mid exposing ( twiceSummed )

                import low ( summed )

                partial let twiceSummed (n: Int) = summed(n) * 2
                """, """
                module top exposing ( Out, bill )

                import mid ( twiceSummed )

                data Out = { v: Int }

                behavior bill : (n: Int) -> Out constructs Out
                let bill (n) = Out { v = twiceSummed(n) }
                """));

        Class<?> fns = new BytesClassLoader(classes, getClass().getClassLoader())
                .loadClass(Emitted.helpers("top"));
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
        Map<String, ClassFileImage> classes = Compiler.compileModules(List.of("""
                module up.a exposing ( step )

                partial let step (n: Int) : Int = if n == 0 then 1 else step(n - 1)
                """, """
                module up.b exposing ( viaStep )

                partial let step (n: Int) : Int = if n == 0 then 2 else step(n - 1)

                partial let viaStep (n: Int) = step(n) * 10
                """, """
                module order exposing ( Out, bill )

                import up.a ( step )
                import up.b ( viaStep )

                data Out = { v: Int }

                behavior bill : (n: Int) -> Out constructs Out
                let bill (n) = Out { v = step(n) + viaStep(n) }
                """));

        assertTrue(classes.containsKey(Emitted.helpers("order")), classes.keySet().toString());
        Class<?> fns = new BytesClassLoader(classes, getClass().getClassLoader())
                .loadClass(Emitted.helpers("order"));
        List<String> methods = java.util.Arrays.stream(fns.getDeclaredMethods())
                .map(java.lang.reflect.Method::getName).sorted().toList();
        assertEquals(List.of("up$a$step", "up$b$step"), methods);
    }

    /** The method goes on the compiling module's own `$Fns`, which stays package-private. A helper's
     * declaring module is its identity, not where its method lives — so publishing one opens no
     * Java-reachable entry, and a construction inside it is no more reachable than before. */
    @Test
    void aCarriedHelperIsEmittedOnThePackagePrivateFnsOfTheReader() throws Exception {
        Map<String, ClassFileImage> classes = Compiler.compileModules(List.of("""
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

        assertTrue(classes.containsKey(Emitted.helpers("order")), classes.keySet().toString());
        Class<?> fns = new BytesClassLoader(classes, getClass().getClassLoader())
                .loadClass(Emitted.helpers("order"));
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
        Map<String, ClassFileImage> classes = Compiler.compile(PRICING);
        ModulePath path = ModulePath.of(classes);

        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module app.billing exposing ( Receipt, bill )

                import pricing ( Amount, taxed )

                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt constructs Receipt
                let bill (a) = Receipt { total = taxed(a) }
                """), path));
    }

    /**
     * And a helper whose signature says {@code Rational} crosses it, which is what moved the boundary
     * version.
     *
     * <p>An exact quotient is a value a computation holds and no boundary carries, so no field and no
     * behavior writes one — but a helper is neither, and a module that works out a ratio for another to
     * narrow writes it in the signature. That spelling has to survive the crossing: written into a class
     * file by one compilation and read back by the next, which is a published signature naming a
     * primitive rather than a declaration of the module it came from.
     */
    @Test
    void aHelperWhoseSignatureSaysRationalCrossesAProjectBoundary() throws Exception {
        Map<String, ClassFileImage> shares = Compiler.compile("""
                module ratio exposing ( share )

                let share (of: Int, among: Int): Rational = of / among
                """);

        BytesClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of("""
                module app.split exposing ( In, Split, apportion )

                import ratio ( share )

                data In = { of: Int, among: Int }
                data Split = { each: Int }

                behavior apportion : (i: In) -> Split constructs Split
                let apportion (i) =
                    Split { each = Rational.toInt(DOWN, share(i.of, i.among)) }
                """), ModulePath.of(shares)), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "app.split.In", Map.of("of", 7L, "among", 2L));
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "app.split.Split",
                Codecs.apply(Emitted.behavior(loader, "app.split", "apportion")
                        .getConstructor().newInstance(), in));
        assertEquals(3L, out.get("each"), "seven halves, taken toward nought");
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

    /** What a published definition stands for is its type, not the constructions its body makes: a
     * return type may name a type the body never builds, and reading the body for constructions
     * answers about a different thing. */
    @Test
    void aPublishedHelperMayNotReturnAHiddenTypeItDoesNotBuild() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( published )

                data Hidden = Int

                let published (n: Int) : List<Hidden> = []
                """));

        assertTrue(e.getMessage().contains("Hidden"), e.getMessage());
    }

    /** A published helper's body runs in the module that calls it, so what the body builds has to be
     * a type that module can reach. The signature names only `Amount`, and the body builds `Step`. */
    @Test
    void aPublishedHelperMayNotBuildATypeTheModuleKeepsToItself() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( Amount, taxed )

                data Amount = Int
                data Step = Int

                let taxed (a: Amount) = Amount(a.value * Step(3).value)
                """));

        assertTrue(e.getMessage().contains("Step"), e.getMessage());
        assertTrue(e.getMessage().contains("taxed"), e.getMessage());
    }

    /** A signature that rests on a type the module keeps is said by the rule about signatures alone.
     * The body builds that type too, and saying it twice would be one mistake reported as two. */
    @Test
    void aHiddenTypeInTheSignatureIsNotAlsoReportedForTheBody() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( wrapped )

                data Hidden = Int

                let wrapped (n: Int) = Hidden(n)
                """));

        assertEquals(List.of("E1611"),
                e.diagnostics().stream().map(d -> d.code().toString()).toList());
    }

    /**
     * Every way a published body comes to name a class its module keeps is refused where the module
     * is compiled, and never reaches the reader's emission.
     *
     * <p>What refuses in the reader is the emitter itself, at the one place a class is named: it
     * throws where the publisher's rule has not been told about a reference. So a shape the rule
     * missed does not pass here as a compile, and does not pass as another failure either — the
     * assertion is on the code, and the emitter's failure has none.
     */
    @Test
    void everyHiddenClassAPublishedBodyNamesIsRefusedWherePublishedAndNotWhereEmitted() {
        String cases = """
                data Email
                data Phone
                data Contact = Email | Phone
                """;
        record Shape(String label, String pricing, String imports, String field, String call) {}
        List<Shape> shapes = List.of(
                new Shape("a construction", """
                        module pricing exposing ( f )

                        data Step = Int

                        let f (n: Int) = Step(n).value
                        """, "f", "n: Int", "f(i.n)"),
                new Shape("a private value that builds", """
                        module pricing exposing ( f )

                        data Step = Int

                        let s = Step(3)
                        let f (n: Int) = n + s.value
                        """, "f", "n: Int", "f(i.n)"),
                new Shape("a unit data as a value", """
                        module pricing exposing ( f )

                        data Marker

                        let f (n: Int) = if Marker == Marker then n else 0
                        """, "f", "n: Int", "f(i.n)"),
                new Shape("a match on hidden cases", """
                        module pricing exposing ( Contact, f )

                        %s
                        let f (c: Contact) =
                            match c with
                                | Email -> 1
                                | Phone -> 2
                        """.formatted(cases), "Contact, f", "c: Contact", "f(i.c)"),
                new Shape("an order taken from a sum whose cases are exposed", """
                        module pricing exposing ( Qualified, Won, before )

                        data Prospecting
                        data Qualified
                        data Won
                        data Stage = Prospecting | Qualified | Won

                        let before (s: Qualified) = s < Won
                        """, "Qualified, before", "s: Qualified", "if before(i.s) then 1 else 0"),
                new Shape("a sort by the order of such a sum", """
                        module pricing exposing ( Qualified, Won, ranked )

                        data Prospecting
                        data Qualified
                        data Won
                        data Stage = Prospecting | Qualified | Won

                        let ranked (n: Int) = List.length(List.sort([Won, Qualified])) + n
                        """, "ranked", "n: Int", "ranked(i.n)"),
                new Shape("a recursive helper the published one reaches", """
                        module pricing exposing ( f )

                        data Step = Int

                        partial let walk (n: Int) : Int = if n == 0 then Step(1).value else walk(n - 1)
                        partial let f (n: Int) = walk(n)
                        """, "f", "n: Int", "f(i.n)"));

        for (Shape shape : shapes) {
            CompileException e = assertThrows(CompileException.class,
                    () -> Compiler.compileModules(List.of(shape.pricing(), """
                            module order exposing ( In, Out, bill )

                            import pricing ( %s )

                            data In = { %s }
                            data Out = { v: Int }

                            behavior bill : (i: In) -> Out constructs Out
                            let bill (i) = Out { v = %s }
                            """.formatted(shape.imports(), shape.field(), shape.call()))),
                    shape.label());
            assertEquals("E1628", e.code(), shape.label() + ": " + e.getMessage());
        }
    }

    /** A helper that is carried and not published is said to be carried: it is not among what the
     * module exposes, and saying it is published would send the author looking for it there. */
    @Test
    void aRecursiveHelperCarriedWithAPublishedOneIsSaidToBeCarried() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( f )

                data Step = Int

                partial let walk (n: Int) : Int = if n == 0 then Step(1).value else walk(n - 1)
                partial let f (n: Int) = walk(n)
                """));

        assertTrue(e.getMessage().contains("walk"), e.getMessage());
        assertTrue(e.getMessage().contains("carried"), e.getMessage());
    }

    /** The order comes from the sum, not from the cases the helper writes, so an exposed sum is a
     * class the reader may name and the same body is published. */
    @Test
    void aPublishedHelperMayTakeAnOrderFromASumTheModuleExposes() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module pricing exposing ( Stage, Qualified, Won, before )

                data Prospecting
                data Qualified
                data Won
                data Stage = Prospecting | Qualified | Won

                let before (s: Qualified) = s < Won
                """, """
                module order exposing ( In, Out, bill )

                import pricing ( Qualified, before )

                data In = { s: Qualified }
                data Out = { v: Int }

                behavior bill : (i: In) -> Out constructs Out
                let bill (i) = Out { v = if before(i.s) then 1 else 0 }
                """)));
    }

    /** A `match` tests the value against the class of each case it names, so a case the module keeps
     * to itself is a reference to a class the reader cannot touch, though nothing in the helper's
     * signature or its constructions names it. The sum may be exposed without its cases. */
    @Test
    void aPublishedHelperMayNotMatchACaseTheModuleKeepsToItself() {
        for (String cases : List.of("""
                data Email
                data Phone
                data Contact = Email | Phone
                """, """
                data Email = { address: String }
                data Phone = { number: String }
                data Contact = Email | Phone
                """)) {
            CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                    module pricing exposing ( Contact, kind )

                    %s
                    let kind (c: Contact) =
                        match c with
                            | Email -> 1
                            | Phone -> 2
                    """.formatted(cases)));

            assertEquals("E1628", e.code(), e.getMessage());
            assertTrue(e.getMessage().contains("Email"), e.getMessage());
        }
    }

    /** And a case the module exposes is public, so the reader may test against it. */
    @Test
    void aPublishedHelperMayMatchACaseTheModuleExposes() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module pricing exposing ( Contact, Email, Phone, kind )

                data Email
                data Phone
                data Contact = Email | Phone

                let kind (c: Contact) =
                    match c with
                        | Email -> 1
                        | Phone -> 2
                """, """
                module order exposing ( In, Out, bill )

                import pricing ( Contact, kind )

                data In = { c: Contact }
                data Out = { v: Int }

                behavior bill : (i: In) -> Out constructs Out
                let bill (i) = Out { v = kind(i.c) }
                """)));
    }

    /** A unit data is read from the shared instance of its class, which is as much a reference to
     * that class as a construction is. */
    @Test
    void aPublishedHelperMayNotNameAUnitDataTheModuleKeepsToItself() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( doubled )

                data Marker

                let doubled (n: Int) = if Marker == Marker then n * 2 else n
                """));

        assertEquals("E1628", e.code(), e.getMessage());
        assertTrue(e.getMessage().contains("Marker"), e.getMessage());
    }

    /** And an exposed one is public, so the reader runs the body that reads it. */
    @Test
    void aPublishedHelperMayNameAUnitDataTheModuleExposesAndItRuns() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of("""
                module pricing exposing ( Marker, doubled )

                data Marker

                let doubled (n: Int) = if Marker == Marker then n * 2 else n
                """, """
                module order exposing ( In, Out, bill )

                import pricing ( doubled )

                data In = { n: Int }
                data Out = { v: Int }

                behavior bill : (i: In) -> Out constructs Out
                let bill (i) = Out { v = doubled(i.n) }
                """)), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "order.In", Map.of("n", 5L));
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "order.Out",
                Codecs.apply(Emitted.behavior(loader, "order", "bill")
                        .getConstructor().newInstance(), in));
        assertEquals(10L, out.get("v"));
    }

    /** A private value a published helper names is expanded into the helper, so what that value
     * builds is what the helper builds. */
    @Test
    void aPublishedHelperMayNotNameAValueThatBuildsATypeTheModuleKeepsToItself() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( Amount, taxed )

                data Amount = Int
                data Rate = Int

                let rate = Rate(10)
                let taxed (a: Amount) = Amount(a.value * rate.value)
                """));

        assertTrue(e.getMessage().contains("Rate"), e.getMessage());
    }

    /** A published value runs in the module that declares it, so what its body builds stays that
     * module's and its reader is handed the answer. */
    @Test
    void aPublishedValueMayBuildATypeTheModuleKeepsToItself() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of("""
                module pricing exposing ( step )

                data Step = Int

                let step = Step(3).value
                """, """
                module order exposing ( In, Out, bill )

                import pricing ( step )

                data In = { n: Int }
                data Out = { v: Int }

                behavior bill : (i: In) -> Out constructs Out
                let bill (i) = Out { v = i.n * step }
                """)), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "order.In", Map.of("n", 5L));
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "order.Out",
                Codecs.apply(Emitted.behavior(loader, "order", "bill")
                        .getConstructor().newInstance(), in));
        assertEquals(15L, out.get("v"));
    }

    /** The same holds of a value, which is the definition with no parameter list. */
    @Test
    void aPublishedValueMayNotStandForAHiddenTypeItDoesNotBuild() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( published )

                data Hidden = Int

                let published : List<Hidden> = []
                """));

        assertTrue(e.getMessage().contains("Hidden"), e.getMessage());
    }

    /** And of a hidden unit data, which a definition stands for by naming it. */
    @Test
    void aPublishedHelperMayNotReturnAHiddenUnitData() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( published )

                data Marker

                let published (n: Int) = Marker
                """));

        assertTrue(e.getMessage().contains("Marker"), e.getMessage());
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

    /** A module that publishes nothing recursive and reaches no value emits no `$Fns` at all — the
     * class appears because a method has to go somewhere, not because a helper was imported. */
    @Test
    void aReaderOfANonRecursiveHelperEmitsNoFnsClass() throws Exception {
        Map<String, ClassFileImage> classes = Compiler.compileModules(List.of("""
                module pricing exposing ( Amount, taxed )

                data Amount = Int

                let taxed (a: Amount) = Amount(a.value * 2)
                """, """
                module order exposing ( Receipt, bill )

                import pricing ( Amount, taxed )

                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt constructs Receipt
                let bill (a) = Receipt { total = taxed(a) }
                """));

        assertFalse(classes.containsKey(Emitted.helpers("order")), classes.keySet().toString());
    }

    /** A helper is expanded into its reader together with what it names, so a value it names that
     * the module does not expose is not something the module publishes: no class of the module
     * offers it to be called, and the reader emits no method for it either. */
    @Test
    void aValueOnlyAPublishedHelperNamesIsExpandedWithTheHelperAndNotOffered() throws Exception {
        Map<String, ClassFileImage> classes = Compiler.compileModules(List.of(PRICING, """
                module order exposing ( Receipt, bill )

                import pricing ( Amount, taxed )

                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt constructs Receipt
                let bill (a) = Receipt { total = taxed(a) }
                """));

        assertFalse(classes.containsKey("pricing.$Values"), classes.keySet().toString());
        assertFalse(classes.containsKey(Emitted.helpers("order")), classes.keySet().toString());
    }

    // --- a helper whose element its body left open ---

    /** A published helper that names its container and not what it holds. Nothing about it is
     * written: the reader settles it from the same body, by the same rule. */
    private static final String COUNTING = """
            module counting exposing ( count )

            let count (xs) = List.length(xs)
            """;

    @Test
    void aHelperWhoseElementIsOpenIsPublishedAndUsedAtTwoElementTypes() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(COUNTING, """
                module report exposing ( Counted, tally )

                import counting ( count )

                data Counted = { n: Int }

                behavior tally : (ns: List<Int>) -> Counted constructs Counted
                let tally (ns) = Counted { n = count(ns) + count([ "a", "b" ]) }
                """)));
    }

    /** Two readers, each at its own element type. A variable held anywhere but in the definition
     * that carries it would be settled by whichever module was compiled first. */
    @Test
    void twoReadersUseOnePublishedHelperAtDifferentElementTypes() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(COUNTING, """
                module ints exposing ( Ints, countInts )
                import counting ( count )
                data Ints = { n: Int }
                behavior countInts : (ns: List<Int>) -> Ints constructs Ints
                let countInts (ns) = Ints { n = count(ns) }
                """, """
                module texts exposing ( Texts, countTexts )
                import counting ( count )
                data Texts = { n: Int }
                behavior countTexts : (ss: List<String>) -> Texts constructs Texts
                let countTexts (ss) = Texts { n = count(ss) }
                """)));
    }

    /**
     * Across a project boundary the helper travels as the source its author wrote, which carries no
     * annotation at all, and the reader's own front end settles it again. So nothing has to write a
     * type variable for it to cross — and the reader still may not write one itself.
     */
    @Test
    void aHelperWhoseElementIsOpenCrossesAProjectBoundary() {
        Map<String, ClassFileImage> library = Compiler.compile(COUNTING);
        ModulePath path = ModulePath.of(library);

        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module app.report exposing ( Counted, tally )

                import counting ( count )

                data Counted = { n: Int }

                behavior tally : (ns: List<Int>) -> Counted constructs Counted
                let tally (ns) = Counted { n = count(ns) + count([ "a" ]) }
                """), path));

        CompileException written = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module app.written
                        import counting ( count )
                        data N = Int
                        behavior go : (n: N) -> N constructs N
                        let sized (xs: List<'a>) = count(xs)
                        let go (n) = N(sized([ 1 ]))
                        """), path));
        assertInstanceOf(ParseMessage.ATypeVariableIsOnlyAllowedInTheCore.class,
                written.diagnostic().said(), written.getMessage());
    }
}
