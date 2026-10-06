package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Which values a module reaches whose body states a type, read before any row or fake names one —
 * {@link TypedFixtureValues}, read off {@link CheckSurface#typedFixtureValues}.
 *
 * <p>A value of a parameter's type that the module states is a candidate however the {@code let}
 * that states it was written: {@code let vip = Customer { ... }} and {@code let vip = makeCustomer
 * (...)} are the same value of the same type declared two ways, and a walk that reads a helper
 * application no differently from a construction offers the same candidate for both — which is what
 * this holds, migrated from the search that used to compute this itself
 * ({@code AValueTheModuleStatesIsOneHoweverItsLetWasWrittenTest}) to the assembly that now discovers
 * it before {@code CheckSurface} mints a single fixture entry.
 */
class CheckSurfaceOffersEveryValueTheModuleStatesAsATypedFixtureValueTest {

    private static final String CONSTRUCTED = model("""
            let vip = Customer { grade = Gold }
            """);

    private static final String CALLED = model("""
            let of (g: Grade) = Customer { grade = g }

            let vip = of(Gold)
            """);

    private static final String IMPORTED = """
            module example.other exposing ( Grade, Customer, vip )

            data Grade = Bronze | Gold
            data Customer = { grade: Grade }

            let vip = Customer { grade = Gold }
            """;

    private static final String IMPORTING = """
            module example.member exposing ( admit )

            import example.other ( Grade, Customer, vip )

            data Accepted = { at: String }

            behavior admit : (customer: Customer) -> Accepted
                constructs Accepted

            let admit (customer) = Accepted { at = "now" }
            """;

    private static String model(String values) {
        return """
                module example.member

                data Bronze
                data Gold
                data Grade = Bronze | Gold

                data Customer = { grade: Grade }

                data Accepted = { at: String }

                behavior admit : (customer: Customer) -> Accepted
                    constructs Accepted

                let admit (customer) = Accepted { at = "now" }

                """ + values;
    }

    /** A value written as a construction is a candidate of the type it builds. */
    @Test
    void aValueWrittenAsAConstructionIsACandidate() {
        assertEquals(List.of(new ReachName.Own(new ValueName.Helper("example.member", "vip"))),
                candidatesOf(CONSTRUCTED, "example.member"));
    }

    /** And so is the same value written as a call of something that constructs one. */
    @Test
    void andSoIsOneWrittenAsACallOfSomethingThatConstructsOne() {
        assertEquals(List.of(new ReachName.Own(new ValueName.Helper("example.member", "vip"))),
                candidatesOf(CALLED, "example.member"));
    }

    private static final String HELPER_LIB = """
            module example.lib exposing ( Grade, Customer, Gold, of )

            data Bronze
            data Gold
            data Grade = Bronze | Gold
            data Customer = { grade: Grade }

            let of (g: Grade) = Customer { grade = g }
            """;

    private static final String CALLED_AN_IMPORTED_HELPER = """
            module example.calls

            import example.lib ( Grade, Customer, Gold, of )

            data Accepted = { at: String }

            behavior admit : (customer: Customer) -> Accepted
                constructs Accepted

            let admit (customer) = Accepted { at = "now" }

            let vip = of(Gold)
            """;

    /**
     * An own value's body applying an imported helper is a candidate too — read through {@code
     * importedForEvidence} and not lost the way {@code values.get(callee.name())} would lose it
     * without an entry for {@code of} at all.
     *
     * <p>{@code vip} is {@code example.calls}' own — the same as {@link
     * #andSoIsOneWrittenAsACallOfSomethingThatConstructsOne}, except the value it calls is declared
     * in {@code example.lib} and not here. Nothing about being a candidate turns on where the
     * declaration that decides {@code vip}'s type lives, only on where {@code vip} itself does.
     */
    @Test
    void anOwnValueCallingAnImportedHelperIsACandidate() {
        Compilation compilation = Compilation.ofSources(
                List.of(HELPER_LIB, CALLED_AN_IMPORTED_HELPER), ModulePath.EMPTY);
        compilation.answerEverything();
        CheckSurface surface = compilation.db()
                .ask(new Shapes.CheckSurface("example.calls")).value();
        assertNotNull(surface, "the module under test does not get as far as being assembled");

        assertEquals(List.of(new ReachName.Own(new ValueName.Helper("example.calls", "vip"))),
                surface.typedFixtureValues().getOrDefault(customerType(compilation,
                        "example.calls"), List.of()));
    }

    private static final String HELPER_LIB_A_CHAIN_DEEP = """
            module example.lib exposing ( Grade, Customer, Gold, of )

            data Bronze
            data Gold
            data Grade = Bronze | Gold
            data Customer = { grade: Grade }

            let make (g: Grade) = Customer { grade = g }
            let of (g: Grade) = make(g)
            """;

    /**
     * An own value calling an imported helper whose own body calls a second, unexposed helper of
     * the same module is a candidate too — {@code make} is never named in an import line, only
     * reached through {@code of}'s own body, the way {@link Bodies.ImportedDefinitions}'s own
     * closure reaches a helper a published body calls in turn.
     *
     * <p>{@link Bodies#publishedByQualifiedName} closes {@code of}'s body against {@code
     * example.lib}'s own expansion table the same way {@link Bodies.ImportedDefinitions} would —
     * {@code Settled}/{@code Expanding} of {@code example.lib}, never of {@code example.calls} —
     * so {@code DeclaredTypeReading} reads past {@code make(g)} the same as it reads past a call
     * this module makes of its own helper.
     */
    @Test
    void anOwnValueCallingAnImportedHelperThatCallsAFurtherHelperIsACandidate() {
        Compilation compilation = Compilation.ofSources(
                List.of(HELPER_LIB_A_CHAIN_DEEP, CALLED_AN_IMPORTED_HELPER), ModulePath.EMPTY);
        compilation.answerEverything();
        CheckSurface surface = compilation.db()
                .ask(new Shapes.CheckSurface("example.calls")).value();
        assertNotNull(surface, "the module under test does not get as far as being assembled");

        assertEquals(List.of(new ReachName.Own(new ValueName.Helper("example.calls", "vip"))),
                surface.typedFixtureValues().getOrDefault(customerType(compilation,
                        "example.calls"), List.of()));
    }

    /**
     * An imported value of a parameter's own type is as much a stated origin as one this module
     * writes itself — the same way a row naming an imported value bare is read no differently from
     * one naming its own. {@link TypedFixtureValues#of} reads {@code importedForEvidence} — a
     * cycle-safe stand-in for {@code Bodies.ImportedDefinitions} ({@link Bodies#publishedByQualifiedName})
     * — as {@link HelperTable}'s own imported map rather than only as evidence for reading an own
     * candidate's body, so {@code vip} reaches this module under {@code example.other}'s own {@link
     * Hir.FnDef#takenOnAs()} the same way any other imported name would.
     */
    @Test
    void anImportedValueIsACandidate() {
        Compilation compilation = Compilation.ofSources(List.of(IMPORTED, IMPORTING),
                ModulePath.EMPTY);
        compilation.answerEverything();
        CheckSurface surface = compilation.db()
                .ask(new Shapes.CheckSurface("example.member")).value();
        assertNotNull(surface, "the module under test does not get as far as being assembled");

        Type customer = customerType(compilation, "example.member");
        assertEquals(List.of(new ReachName.OfModule(new ValueName.Helper("example.other", "vip"))),
                surface.typedFixtureValues().getOrDefault(customer, List.of()));
    }

    /**
     * A nullary value whose body builds a type nothing here takes or answers is not a candidate,
     * even though its type reads fine on its own — {@code #of}'s own narrowing and not a side
     * effect of anything failing to read.
     */
    @Test
    void aValueOfATypeNoBehaviorTakesOrAnswersIsNotACandidate() {
        String source = model("""
                data Irrelevant = { x: Int }

                let vip = Customer { grade = Gold }
                let junk = Irrelevant { x = 1 }
                """);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        CheckSurface surface = compilation.db()
                .ask(new Shapes.CheckSurface("example.member")).value();
        assertNotNull(surface, "the module under test does not get as far as being assembled");

        for (List<ReachName.Declaration> candidates : surface.typedFixtureValues().values()) {
            for (ReachName.Declaration candidate : candidates) {
                assertNotNull(candidate.denotes());
                assertEquals(new ValueName.Helper("example.member", "vip"), candidate.denotes(),
                        "`junk` builds a type no behavior here takes or answers, so it is not"
                                + " among the candidates however cleanly its own type reads");
            }
        }
    }

    /**
     * A declaration elsewhere that does not read does not stop the search from finding a candidate
     * whose own type reads fine — {@link FieldRead.Unreadable#MAKES_NOTHING_READABLE} answers
     * nothing for the one that fails rather than raising and losing every other candidate with it.
     *
     * <p>{@code stray}'s body reads a field of {@code A}, whose two same-named fields are exactly
     * the declaration {@code WhatADotMayNameIsOneAnswerForEveryReaderOfItTest} holds to answering
     * nothing for a text still being typed. Nullary and reached the same way {@code vip} is, it is
     * walked by the same {@code DeclaredTypeReading} — the read the old {@code REFUSED} wiring would
     * have raised over, taking {@code vip} down with it.
     */
    @Test
    void aDeclarationElsewhereThatDoesNotReadDoesNotLoseAGoodCandidate() {
        String source = model("""
                data A = { x: Int, x: String }

                let vip = Customer { grade = Gold }
                let stray = A { x = 1 }.x
                """);
        // Asked directly and not through Compilation.answerEverything(): the full pipeline reaches
        // A's declaration too, at a rung that does refuse a field declared twice, and this test is
        // about CheckSurface's own tolerance and not about whether the module as a whole checks.
        Compilation compilation = Compilation.ofSource(source, "Main");
        CheckSurface surface = compilation.db()
                .ask(new Shapes.CheckSurface("example.member")).value();
        assertNotNull(surface, "a declaration elsewhere that does not read still lets the module"
                + " assemble");
        assertEquals(List.of(new ReachName.Own(new ValueName.Helper("example.member", "vip"))),
                surface.typedFixtureValues().getOrDefault(customerType(compilation,
                        "example.member"), List.of()));
    }

    /**
     * A nullary value of a behavior's own declared output type is not a candidate — only an input
     * type is, the domain {@code Adequacy.Generated.named} has always read a baseline from.
     */
    @Test
    void aValueOfABehaviorsOutputTypeIsNotACandidate() {
        String source = model("""
                let vip = Customer { grade = Gold }
                let junk = Accepted { at = "x" }
                """);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        CheckSurface surface = compilation.db()
                .ask(new Shapes.CheckSurface("example.member")).value();
        assertNotNull(surface, "the module under test does not get as far as being assembled");

        for (List<ReachName.Declaration> candidates : surface.typedFixtureValues().values()) {
            for (ReachName.Declaration candidate : candidates) {
                assertEquals(new ValueName.Helper("example.member", "vip"), candidate.denotes(),
                        "`junk` builds `admit`'s own output type, which is not among the types a"
                                + " row may spread it over");
            }
        }
    }

    private static final String TAKES_A_LIST = """
            module example.member

            data Bronze
            data Gold
            data Grade = Bronze | Gold

            data Customer = { grade: Grade }

            data Accepted = { at: String }

            behavior admitAll : (customers: List<Customer>) -> Accepted
                constructs Accepted

            let admitAll (customers) = Accepted { at = "now" }

            let vip = Customer { grade = Gold }

            """;

    /**
     * A value written at the list type a parameter takes is a candidate for that parameter. What
     * makes it one is that its type is the parameter's, and a type with no name of its own is a
     * type a parameter is declared at as much as a record is.
     */
    @Test
    void aValueWrittenAtAParametersListTypeIsACandidate() {
        Compilation compilation = Compilation.ofSource(TAKES_A_LIST + """
                let regulars: List<Customer> = [ vip, vip ]
                """, "Main");
        compilation.answerEverything();
        CheckSurface surface = compilation.db()
                .ask(new Shapes.CheckSurface("example.member")).value();
        assertNotNull(surface, "the module under test does not get as far as being assembled");
        Type taken = parameterType(compilation, "example.member", "admitAll");
        assertInstanceOf(Type.ListOf.class, taken, "the parameter is a list");

        assertEquals(List.of(new ReachName.Own(new ValueName.Helper("example.member", "regulars"))),
                surface.typedFixtureValues().getOrDefault(taken, List.of()));
    }

    /**
     * And not where the type is left to the elements. A list written out is the join of what it
     * holds, which no declaration states, so a value whose declaration names no type has none to
     * be offered under.
     */
    @Test
    void aListWhoseDeclarationNamesNoTypeIsNotACandidate() {
        Compilation compilation = Compilation.ofSource(TAKES_A_LIST + """
                let regulars = [ vip, vip ]
                """, "Main");
        compilation.answerEverything();
        CheckSurface surface = compilation.db()
                .ask(new Shapes.CheckSurface("example.member")).value();
        assertNotNull(surface, "the module under test does not get as far as being assembled");

        assertEquals(List.of(), surface.typedFixtureValues().getOrDefault(
                parameterType(compilation, "example.member", "admitAll"), List.of()));
    }

    private static final String STAGE = """
            module example.stage exposing ( Raw, Mid, first )

            data Raw = { n: Int }
            data Mid = { n: Int }

            behavior first : (raw: Raw) -> Mid
                constructs Mid

            let first (raw) = Mid { n = raw.n }
            """;

    private static final String COMPOSED = """
            module example.composed exposing ( admit )

            import example.stage ( Raw, Mid, first )

            data Grade = Bronze | Gold
            data Customer = { grade: Grade }
            data Accepted = { at: String }

            behavior admit : (customer: Customer) -> Accepted
                constructs Accepted

            let admit (customer) = Accepted { at = "now" }

            behavior finish : (m: Mid) -> Accepted
                constructs Accepted

            let finish (m) = Accepted { at = "done" }

            behavior process = first >-> finish

            let junk = Raw { n = 1 }
            """;

    /**
     * A nullary value of {@code Raw} is not a candidate: {@code Raw} reaches this module's own
     * behaviors only through {@code process}, a {@code >->} composition, and {@code
     * Adequacy.Generated} never generates a row against a composition directly — {@code specOf}
     * answers null for anything but a {@code SpecBehavior}, and generation stops there. A
     * composition's input is its first stage's own ({@code first}, borrowed and not declared here),
     * so nothing this module declares takes a {@code Raw} the way a row could be composed against
     * it.
     */
    @Test
    void aValueOfACompositionsInputTypeIsNotACandidate() {
        Compilation compilation = Compilation.ofSources(List.of(STAGE, COMPOSED),
                ModulePath.EMPTY);
        compilation.answerEverything();
        CheckSurface surface = compilation.db()
                .ask(new Shapes.CheckSurface("example.composed")).value();
        assertNotNull(surface, "the module under test does not get as far as being assembled");

        ValueName.Helper junk = new ValueName.Helper("example.composed", "junk");
        for (List<ReachName.Declaration> candidates : surface.typedFixtureValues().values()) {
            for (ReachName.Declaration candidate : candidates) {
                assertNotNull(candidate.denotes());
                if (candidate.denotes().equals(junk)) {
                    throw new AssertionError("`junk` builds `Raw`, which only a composition takes"
                            + " here, so it should not be among the candidates: "
                            + surface.typedFixtureValues());
                }
            }
        }
    }

    private static List<ReachName.Declaration> candidatesOf(String source, String module) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        CheckSurface surface = compilation.db().ask(new Shapes.CheckSurface(module)).value();
        assertNotNull(surface, "the module under test does not get as far as being assembled");
        return surface.typedFixtureValues().getOrDefault(customerType(compilation, module),
                List.of());
    }

    /** The behavior under test's own parameter type, read the way {@code Adequacy} reads it. */
    private static Type customerType(Compilation compilation, String module) {
        Type taken = parameterType(compilation, module, "admit");
        if (taken instanceof Type.Ref) {
            return taken;
        }
        throw new AssertionError("`admit` takes a resolved `Customer`: " + taken);
    }

    /** The first parameter type of {@code behavior}, as its signature declares it. */
    private static Type parameterType(Compilation compilation, String module, String behavior) {
        Sig sig = compilation.db().ask(new Bodies.Signatures(module)).value().get(behavior);
        assertNotNull(sig, "the behavior under test has a signature");
        return sig.inputTypes().get(0);
    }
}
