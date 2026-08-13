package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A module publishes its values. A value is part of what a module offers — a limit a rule is written
 * against, the representative record an example is stated with — and a reader of that module had to
 * write it out again, which is what left an import list naming ten types for one fixture (issue
 * #163).
 *
 * <p>A published value's own type must be published; the types its body happens to use are its own
 * business. What a module publishes besides its values — its helpers — is
 * {@link CompilePublishedHelperTest}'s.
 */
class CompileExposedValueTest {

    private static final String UPSTREAM = """
            module pricing exposing ( Amount, Priced, cap, standard )

            data Amount = Int
            data Priced = { total: Amount, note: String }

            let cap = Amount(1000)
            let standard = Priced { total = cap, note = "standard" }
            """;

    @Test
    void aValueIsPublishedAndReadInAnotherModule() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(UPSTREAM, """
                module order exposing ( Receipt, bill )

                import pricing ( Amount, Priced, cap )

                data Receipt = { total: Amount }

                behavior bill : (p: Priced) -> Receipt constructs Receipt, Amount
                let bill (p) = Receipt { total = Amount(p.total.value + cap.value) }
                """)));
    }

    /** The point of publishing a value: a row names it instead of restating the record, and the
     * importing module names one type rather than every type inside it. */
    @Test
    void anExampleRowNamesAnImportedValue() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(UPSTREAM, """
                module order exposing ( Receipt, bill )

                import pricing ( Priced, standard )

                data Receipt = { note: String }

                behavior bill : (p: Priced) -> Receipt constructs Receipt
                let bill (p) = Receipt { note = p.note }

                example bill
                    | "the standard price is billed by its note" : (standard)
                        -> Receipt { note = "standard" }
                """)));
    }

    @Test
    void anImportedValueMayBeSpread() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(UPSTREAM, """
                module order exposing ( bill )

                import pricing ( Amount, Priced, standard )

                behavior bill : (p: Priced) -> Priced constructs Priced, Amount
                let bill (p) = Priced { ...standard, note = "billed" }
                """)));
    }

    @Test
    void aPublishedValueMustHaveAPublishedType() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( cap )

                data Amount = Int

                let cap = Amount(1000)
                """));

        assertTrue(e.getMessage().contains("Amount"), e.getMessage());
    }

    /** Only the value's own type crosses. What its body reached for on the way is not the reader's
     * concern, and requiring it would put every inner type back in the import list. */
    @Test
    void aTypeUsedOnlyInsideAPublishedValuesBodyStaysUnpublished() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module pricing exposing ( Amount, cap )

                data Amount = Int
                data Step = Int

                let base = Step(10)
                let cap = Amount(base.value * 100)
                """));
    }

    /** A `let` written as a lambda is a helper, not a value holding a function — the parameter list is
     * where it is written, not what shape it is written in. Publishing it publishes the helper. */
    @Test
    void aLetWrittenAsALambdaIsPublishedAsTheHelperItIs() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module pricing exposing ( Amount, raise )

                data Amount = Int

                let raise = (a) -> a + 1
                """));
    }

    /** A value crosses a project boundary too: what is published is the declaration, read back from
     * the jar, and a value is substituted from that like any other. */
    @Test
    void aValueCrossesAProjectBoundary() throws Exception {
        Map<String, byte[]> classes = Compiler.compile(UPSTREAM);
        ModulePath path = classes::get;

        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module app.billing exposing ( Receipt, bill )

                import pricing ( Amount, Priced, cap )

                data Receipt = { total: Amount }

                behavior bill : (p: Priced) -> Receipt constructs Receipt, Amount
                let bill (p) = Receipt { total = Amount(p.total.value + cap.value) }
                """), path));
    }

    /**
     * A published value means what it meant where it was written. Its body's names were resolved
     * there, and a definition the reader happens to spell the same way is a different definition.
     */
    @Test
    void aPublishedValueKeepsItsOwnDependenciesWhenAReaderSharesTheirNames() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of("""
                module pricing exposing ( Amount, standard )

                data Amount = Int

                let base = 10
                let standard = Amount(base)
                """, """
                module order exposing ( In, Out, bill )

                import pricing ( Amount, standard )

                data In = { n: Int }
                data Out = { v: Int }

                let base = 999

                behavior bill : (i: In) -> Out constructs Out, Amount
                let bill (i) = Out { v = standard.value }
                """)), getClass().getClassLoader());

        Object behavior = Emitted.behavior(loader, "order", "bill").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, Codecs.decoded(loader, "order.In", Map.of("n", 1L)));

        assertEquals(10L, ((Map<?, ?>) Codecs.encode(loader, "order.Out", out)).get("v"));
    }

    /** Two published values, each resting on its own module's `step`. */
    @Test
    void twoPublishedValuesKeepTheirOwnDependenciesOfOneName() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of("""
                module left exposing ( Amount, one )
                data Amount = Int
                let step = 1
                let one = Amount(step)
                """, """
                module right exposing ( Count, two )
                data Count = Int
                let step = 2
                let two = Count(step)
                """, """
                module app exposing ( In, Out, bill )

                import left ( Amount, one )
                import right ( Count, two )

                data In = { n: Int }
                data Out = { v: Int }

                behavior bill : (i: In) -> Out constructs Out, Amount, Count
                let bill (i) = Out { v = one.value + two.value }
                """)), getClass().getClassLoader());

        Object behavior = Emitted.behavior(loader, "app", "bill").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, Codecs.decoded(loader, "app.In", Map.of("n", 1L)));

        assertEquals(3L, ((Map<?, ?>) Codecs.encode(loader, "app.Out", out)).get("v"));
    }

    /** The rule is about what the value is, so reaching the hidden type through another value does
     * not get round it. */
    @Test
    void aPublishedValueMayNotStandForAHiddenTypeThroughAnotherValue() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( published )

                data Hidden = Int

                let privateValue = Hidden(1000)
                let published = privateValue
                """));

        assertTrue(e.getMessage().contains("Hidden"), e.getMessage());
    }

    @Test
    void aPublishedValueMayNotStandForAHiddenTypeThroughAHelper() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( published )

                data Hidden = Int

                let make (n: Int) = Hidden(n)
                let published = make(1000)
                """));

        assertTrue(e.getMessage().contains("Hidden"), e.getMessage());
    }

    /**
     * A behavior taking nothing is implemented by a value, but the behavior is what is published —
     * a reader calls it, and never reads the body it was given. Publishing the body would put an
     * implementation where a specification goes, and let a row name it as a fixture.
     */
    @Test
    void aBehaviorImplementedByAValueDoesNotPublishItsBody() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module clock exposing ( D, now )

                        data D = { v: Int }

                        behavior now : () -> D constructs D
                        let now = D { v = 1 }
                        """, """
                        module app exposing ( Out, go )

                        import clock ( D, now )

                        data Out = { v: Int }

                        behavior go : (d: D) -> Out constructs Out
                        let go (d) = Out { v = d.v }

                        example go
                            | "a behavior is not a fixture" : (now) -> Out { v = 1 }
                        """)));

        assertTrue(e.getMessage().contains("now"), e.getMessage());
    }

    /** A published value may reach a recursive helper: what closing leaves standing is a call, and the
     * helper it calls comes along to be emitted as one of the reader's own methods. */
    @Test
    void aPublishedValueMayReachARecursiveHelper() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module pricing exposing ( Amount, standard )

                data Amount = Int

                partial let sumDown (n: Int) : Int = if n == 0 then 0 else n + sumDown(n - 1)

                partial let standard = Amount(sumDown(10))
                """));
    }

    /** The reader having a helper of that name changes nothing: what crosses is the declaring
     * module's, named by that module, so the two never meet. */
    @Test
    void aCarriedRecursiveHelperIsNotTheReadersHelperOfThatName() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module pricing exposing ( Amount, standard )

                data Amount = Int

                partial let sumDown (n: Int) : Int = if n == 0 then 0 else n + sumDown(n - 1)

                partial let standard = Amount(sumDown(10))
                """, """
                module order exposing ( In, Out, bill )

                import pricing ( Amount, standard )

                data In = { n: Int }
                data Out = { v: Int }

                partial let sumDown (n: Int) : Int = if n == 0 then 999 else sumDown(n - 1)

                behavior bill : (i: In) -> Out constructs Out
                let bill (i) = Out { v = standard.value + sumDown(i.n) }
                """)));
    }

    /** The surface rule reaches through a recursive helper by reading what it returns: the helper is
     * not expanded, so a construction inside it is not there to be read off. */
    @Test
    void aPublishedValueMayNotStandForAHiddenTypeThroughARecursiveHelper() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module pricing exposing ( published )

                data Hidden = Int

                partial let make (n: Int) : Hidden = if n == 0 then Hidden(0) else make(n - 1)

                partial let published = make(10)
                """));

        assertTrue(e.getMessage().contains("Hidden"), e.getMessage());
        assertTrue(e.getMessage().contains("published"), e.getMessage());
    }

    /** A value another module keeps to itself has no name here, as any unexposed name has. */
    @Test
    void anUnpublishedValueCannotBeImported() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of("""
                        module pricing exposing ( Amount )

                        data Amount = Int

                        let cap = Amount(1000)
                        """, """
                        module order exposing ( bill )

                        import pricing ( Amount, cap )

                        behavior bill : (a: Amount) -> Amount constructs Amount
                        let bill (a) = Amount(a.value + cap.value)
                        """)));

        assertTrue(e.getMessage().contains("cap"), e.getMessage());
    }
}
