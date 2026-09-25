package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.nio.charset.StandardCharsets;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
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
        Map<String, ClassFileImage> classes = Compiler.compile(UPSTREAM);
        ModulePath path = ModulePath.of(classes);

        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module app.billing exposing ( Receipt, bill )

                import pricing ( Amount, Priced, cap )

                data Receipt = { total: Amount }

                behavior bill : (p: Priced) -> Receipt constructs Receipt, Amount
                let bill (p) = Receipt { total = Amount(p.total.value + cap.value) }
                """), path));
    }

    private static final String UPSTREAM_WITH_NO_CLAUSE = """
            module pricing

            data Amount = Int
            data Priced = { total: Amount, note: String }

            let cap = Amount(1000)
            let doubled (a: Amount) : Amount = Amount(a.value * 2)
            """;

    private static final String READER_OF_NO_CLAUSE = """
            module order exposing ( Receipt, bill )

            import pricing ( Amount, Priced, cap, doubled )

            data Receipt = { total: Amount }

            behavior bill : (p: Priced) -> Receipt constructs Receipt, Amount
            let bill (p) = Receipt { total = doubled(Amount(p.total.value + cap.value)) }
            """;

    /** A module that writes no clause publishes every declaration it makes, its values and helpers
     *  among them (spec §a-module-publishes-what-it-declares). */
    @Test
    void aModuleWritingNoClausePublishesItsValuesAndHelpers() {
        assertDoesNotThrow(() -> Compiler.compileModules(
                List.of(UPSTREAM_WITH_NO_CLAUSE, READER_OF_NO_CLAUSE)));
    }

    /** And the jar it compiles to carries them, as it does for a module whose clause names them. */
    @Test
    void whatAModuleWritingNoClausePublishesCrossesAProjectBoundary() throws Exception {
        ModulePath path = ModulePath.of(Compiler.compile(UPSTREAM_WITH_NO_CLAUSE));

        assertDoesNotThrow(() -> Compiler.compileModules(List.of(READER_OF_NO_CLAUSE), path));
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

    /** A published value may reach a recursive helper: what closing leaves standing is a call to the
     * declaring module's own method, which never becomes the reader's. */
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

    /** The reader having a value of the name a published value reaches changes nothing: what the
     * published value names is the declaring module's, so the two never meet. The rows decide it,
     * since a reader that read its own `base` would answer another number. */
    @Test
    void aCarriedValueIsNotTheReadersValueOfThatName() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module pricing exposing ( Amount, standard )

                data Amount = Int
                data Step = Int

                let base = Step(10)
                let standard = Amount(base.value * 100)
                """, """
                module order exposing ( In, Out, bill )

                import pricing ( Amount, standard )

                data In = { n: Int }
                data Out = { v: Int }
                data Step = Int

                let base = Step(7)

                behavior bill : (i: In) -> Out constructs Out
                let bill (i) = Out { v = standard.value + base.value + i.n }

                example bill
                    | "the published value is the declaring module's" : (In { n = 1 })
                        -> Out { v = 1008 }
                """)));
    }

    /** A value runs in the module that declares it even when that module is only a jar. What it is
     * built from stays there, so a type the jar does not expose is never named from the reader,
     * and what the reader types the call by is what the jar recorded the value as. */
    @Test
    void aValueBuiltOfAHiddenTypeRunsAcrossAJarBoundary() throws Exception {
        Map<String, ClassFileImage> jar = Compiler.compile("""
                module pricing exposing ( Amount, cap )

                data Amount = Int
                data Step = Int

                let base = Step(10)
                let cap = Amount(base.value * 100)
                """);
        Map<String, ClassFileImage> reader = Compiler.compileModules(List.of("""
                module order exposing ( In, Out, bill )

                import pricing ( Amount, cap )

                data In = { n: Int }
                data Out = { v: Int }

                behavior bill : (i: In) -> Out constructs Out
                let bill (i) = Out { v = cap.value + i.n }
                """), ModulePath.of(jar));
        Map<String, ClassFileImage> both = new java.util.LinkedHashMap<>(jar);
        both.putAll(reader);
        BytesClassLoader loader = new BytesClassLoader(both, getClass().getClassLoader());

        Object behavior = Emitted.behavior(loader, "order", "bill").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, Codecs.decoded(loader, "order.In", Map.of("n", 0L)));

        assertEquals(1000L, ((Map<?, ?>) Codecs.encode(loader, "order.Out", out)).get("v"));
    }

    private static final String CHAINED = """
            module pricing exposing ( Amount, cap )

            data Amount = Int

            let base = Amount(1000)
            let middle = base
            let cap = middle
            """;

    private static final String CHAIN_READER = """
            module order exposing ( Out, bill )

            import pricing ( Amount, cap )

            data Out = { v: Int }

            behavior bill : (a: Amount) -> Out constructs Out, Amount
            let bill (a) = Out { v = cap.value }
            """;

    /** What a private value the published one rests on builds is still what the reader's
     * behavior is held to, in the same run. */
    @Test
    void aConstructionBehindPrivateValuesIsCountedInTheSameRun() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(CHAINED, CHAIN_READER)));
    }

    /** And from a jar, where only what the module recorded and carried is there. */
    @Test
    void aConstructionBehindPrivateValuesIsCountedAcrossAJar() {
        ModulePath path = ModulePath.of(Compiler.compile(CHAINED));

        assertDoesNotThrow(() -> Compiler.compileModules(List.of(CHAIN_READER), path));
    }

    private static final String OPEN = """
            module pricing

            data Amount = Int

            let cap = Amount(base.value * 100)
            let base = Amount(10)
            """;

    private static final String OPEN_READER = """
            module order exposing ( In, Out, bill )

            import pricing ( cap )

            data In = { n: Int }
            data Out = { v: Int }

            behavior bill : (i: In) -> Out constructs Out
            let bill (i) = Out { v = cap.value + i.n }
            """;

    /** A module that writes no clause publishes its values, so another module calls one through the
     * entry the module publishes for it. */
    @Test
    void aModuleWritingNoClauseOffersItsValuesAndPublishesTheirEntries() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(OPEN, OPEN_READER)));

        assertTrue(Compiler.compile(OPEN).containsKey("pricing.$Values"));
    }

    /** One writing {@code exposing ()} publishes none of them: an importer is refused, and there is
     * no entry to call through. */
    @Test
    void aModuleWritingAnEmptyClauseOffersNoValueAndPublishesNoEntry() {
        String closed = OPEN.replace("module pricing\n", "module pricing exposing ()\n");

        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(closed, OPEN_READER)));
        assertTrue(refused.getMessage().contains("not exposed"), refused.getMessage());

        assertFalse(Compiler.compile(closed).containsKey("pricing.$Values"));
    }

    /** What a module says it settled its values as is what it publishes and nothing more: the
     * definitions written for an example row are not there, so adding an example does not change
     * what the artifact declares. */
    @Test
    void anExampleRowDoesNotChangeWhatAModuleRecordsOfItsValues() {
        String base = """
                module pricing exposing ( Amount, cap, rate )

                data Amount = Int

                let cap = Amount(1000)
                let rate (a: Amount) = Amount(a.value * 2)

                behavior double : (a: Amount) -> Amount
                let double (a) = rate(a)
                """;
        String withExample = base + """

                example double
                    | "twice" : (cap) -> Amount(2000)
                """;

        assertEquals(recorded(Compiler.compile(base)), recorded(Compiler.compile(withExample)));
    }

    private static String recorded(Map<String, ClassFileImage> classes) {
        return java.util.Arrays.toString(classes.get("pricing.$Module").bytes());
    }

    private static final String LIMITS = """
            module up exposing ( Amount, ceiling, computed )

            data Amount = Int

            let ceiling = 1000
            let computed = Amount(ceiling * 2)
            """;

    private static String readerOf(String name) {
        return """
                module down exposing ( In, Out, f )

                import up ( %s )

                data In = { n: Int }
                data Out = { v: Int }

                behavior f : (i: In) -> Out constructs Out
                let f (i) = Out { v = i.n + %s }
                """.formatted(name, name.equals("computed") ? "computed.value" : name);
    }

    private static boolean callsTheEntryOfUp(Map<String, ClassFileImage> classes) {
        return classes.entrySet().stream()
                .filter(e -> e.getKey().startsWith("down."))
                .anyMatch(e -> new String(e.getValue().bytes(), StandardCharsets.ISO_8859_1)
                        .contains("up/$Values"));
    }

    /** What a value is read as depends on what it is and never on where it was declared or how
     * the reader got it. A value that has to be computed is computed where it is declared and
     * called from there; a constant is known when the reader is compiled, is a literal wherever it
     * is named — in its own module as in another — and so is called from nowhere. The same in one
     * run and from a jar. */
    @Test
    void aValueIsCalledAndAConstantIsALiteralWhetherOrNotTheModuleIsAJar() {
        Map<String, ClassFileImage> jar = Compiler.compile(LIMITS);

        for (boolean fromAJar : List.of(false, true)) {
            Map<String, ClassFileImage> constant = fromAJar
                    ? Compiler.compileModules(List.of(readerOf("ceiling")), ModulePath.of(jar))
                    : Compiler.compileModules(List.of(LIMITS, readerOf("ceiling")));
            Map<String, ClassFileImage> computed = fromAJar
                    ? Compiler.compileModules(List.of(readerOf("computed")), ModulePath.of(jar))
                    : Compiler.compileModules(List.of(LIMITS, readerOf("computed")));

            assertTrue(!callsTheEntryOfUp(constant), "a constant is read as a literal, from a jar: " + fromAJar);
            assertTrue(callsTheEntryOfUp(computed), "a value is called, from a jar: " + fromAJar);
        }
    }

    /** A published helper that reaches a private value still runs from another module. */
    @Test
    void aPublishedHelperReachingAPrivateValueRunsInAnotherModule() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of("""
                module pricing exposing ( Amount, taxed )

                data Amount = Int

                let rate = Amount(3)
                let taxed (a: Amount) = Amount(a.value * rate.value)
                """, """
                module order exposing ( In, Out, bill )

                import pricing ( Amount, taxed )

                data In = { n: Int }
                data Out = { v: Int }

                behavior bill : (i: In) -> Out constructs Out, Amount
                let bill (i) = Out { v = taxed(Amount(i.n)).value }
                """)), getClass().getClassLoader());

        Object behavior = Emitted.behavior(loader, "order", "bill").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, Codecs.decoded(loader, "order.In", Map.of("n", 2L)));

        assertEquals(6L, ((Map<?, ?>) Codecs.encode(loader, "order.Out", out)).get("v"));
    }

    /** The JVM surface of `$Values` is the exposed surface: a value the module keeps to itself is
     * not public. */
    @Test
    void onlyAnExposedValueHasAPublicEntry() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of(CHAINED)),
                getClass().getClassLoader());

        Class<?> values = loader.loadClass("pricing.$Values");

        assertTrue(java.lang.reflect.Modifier.isPublic(values.getMethod("cap").getModifiers()));
        assertTrue(java.util.Arrays.stream(values.getDeclaredMethods())
                .filter(m -> !m.getName().equals("cap"))
                .noneMatch(m -> java.lang.reflect.Modifier.isPublic(m.getModifiers())));
    }

    /** A published value is read through a public method of its declaring module that builds it
     * there, so a type that module does not expose is never named from outside it. */
    @Test
    void aPublishedValueIsReadThroughItsDeclaringModulesEntry() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compileModules(List.of("""
                module pricing exposing ( Amount, cap )

                data Amount = Int
                data Step = Int

                let base = Step(10)
                let cap = Amount(base.value * 100)
                """)), getClass().getClassLoader());

        Class<?> values = loader.loadClass("pricing.$Values");
        Object cap = values.getMethod("cap").invoke(null);

        assertTrue(java.lang.reflect.Modifier.isPublic(values.getModifiers()));
        assertEquals(1000L, Codecs.encode(loader, "pricing.Amount", cap));
    }

    /** A value published by name and also reached by another published value is one definition in
     * the reader, and both routes to it answer alike. */
    @Test
    void aValueReachedByNameAndThroughAnotherPublishedValueIsOneDefinition() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module pricing exposing ( Amount, cap, standard )

                data Amount = Int

                let cap = Amount(1000)
                let standard = Amount(cap.value + 1)
                """, """
                module order exposing ( In, Out, bill )

                import pricing ( Amount, cap, standard )

                data In = { n: Int }
                data Out = { v: Int }

                behavior bill : (i: In) -> Out constructs Out
                let bill (i) = Out { v = cap.value + standard.value + i.n }

                example bill
                    | "both routes reach the same value" : (In { n = 1 })
                        -> Out { v = 2002 }
                """)));
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

    /** A published value is emitted whether or not anything in its own module names it, so what
     * it forks on has to be read for it: a module of values alone has no behavior whose check
     * would have. */
    @Test
    void aPublishedValueThatForksIsCompiledInAModuleWithNoBehavior() {
        String forking = """
                module limits exposing ( ceiling, floor )

                let inner = List.length([1, 2, 3]) > 2

                let ceiling = if inner then 100 else 10

                let floor = inner && (if List.length([1]) > 0 then inner else false)
                """;

        Map<String, ClassFileImage> compiled =
                assertDoesNotThrow(() -> Compiler.compile(forking));

        assertTrue(compiled.containsKey("limits.$Values"), compiled.keySet().toString());
    }
}
