package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
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

    /**
     * An imported value is not a candidate yet — {@link TypedFixtureValues#of} is handed no
     * imports to read.
     *
     * <p>This records the current wiring, not the intended language semantics: an imported value
     * of a parameter's own type is as much a stated origin as one this module writes itself, the
     * same way a row naming an imported value bare is read no differently from one naming its own.
     * What stops it today is that reading {@code Bodies.ImportedDefinitions} of this same module
     * from inside {@code Shapes.CheckSurface}'s own producer cycles back into this same {@code
     * CheckSurface}: that key's own closure needs {@code Shapes.ClausesTakenIn}, and asking it here
     * is the shape of cycle {@code DeclaredTypeReading}'s checked-world {@code FieldTypes} already
     * refuses, just reached by a different route. A reader who closes that gap turns this
     * assertion around rather than deleting it quietly — the empty list below is exactly what
     * should stop being empty.
     */
    @Test
    void anImportedValueIsNotACandidateYet() {
        Compilation compilation = Compilation.ofSources(List.of(IMPORTED, IMPORTING),
                ModulePath.EMPTY);
        compilation.answerEverything();
        CheckSurface surface = compilation.db()
                .ask(new Shapes.CheckSurface("example.member")).value();
        assertNotNull(surface, "the module under test does not get as far as being assembled");

        TypeSymbol customer = customerType(compilation, "example.member");
        assertEquals(List.of(), surface.typedFixtureValues().getOrDefault(customer, List.of()));
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
    private static TypeSymbol customerType(Compilation compilation, String module) {
        Sig sig = compilation.db().ask(new Bodies.Signatures(module)).value().get("admit");
        assertNotNull(sig, "the behavior under test has a signature");
        if (sig.inputTypes().get(0) instanceof Type.Ref(TypeSymbol of)) {
            return of;
        }
        throw new AssertionError("`admit` takes a resolved `Customer`: " + sig.inputTypes());
    }
}
