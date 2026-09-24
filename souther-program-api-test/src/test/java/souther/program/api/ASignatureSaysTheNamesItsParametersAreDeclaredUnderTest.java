package souther.program.api;

import souther.compiler.Compiler;
import souther.compiler.core.Core;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.program.BehaviorTarget;
import souther.compiler.program.CheckedImplementation;
import souther.compiler.program.CheckedProgram;
import souther.compiler.program.CheckedSignature;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A checked signature says the names its parameters are declared under, and says where it has
 * none.
 *
 * <p>The names are the signature's, not a body's. A {@code let} binds the inputs by position under
 * names of its own, and a behavior implemented outside Souther binds none — yet a binding generated
 * for it publishes a function whose parameter names are part of its API. A composition writes no
 * parameter list at all, and that is a different answer from a signature that declares {@code ()}.
 */
class ASignatureSaysTheNamesItsParametersAreDeclaredUnderTest {

    private static final String BILLING = """
            module billing

            behavior settle : (line: Int, paid: Int) -> Int
            let settle (l, amount) = l + amount

            behavior doubled : (n: Int) -> Int
            let doubled (n) = n + n

            behavior settledTwice = settle >-> doubled

            behavior rateFor : (of: Int) -> Int

            behavior priced : (base: Int) -> Int
                depends on rateFor
            let priced (base, rateFor) = rateFor(base)

            behavior now : () -> Int
            """;

    /** Published by another project: one behavior it implements under binders of its own, and one
     *  nothing there implements. */
    private static final String PUBLISHED = """
            module lib.rates exposing ( spin, quote, spunTwice : Int )

            behavior spin : (of: Int) -> Int
            let spin (x) = x

            behavior quote : (item: Int, qty: Int) -> Int

            behavior spunTwice = spin >-> spin
            """;

    private static final String USES = """
            module app.uses
            import lib.rates ( spin, quote, spunTwice )

            behavior spun : (base: Int) -> Int
            let spun (base) = spin(base)
            """;

    @Test
    void theNamesAreTheSignaturesAndNotTheBindersOfTheLetImplementingIt() {
        BehaviorTarget settle = CheckedProgram.of(List.of(BILLING))
                .behavior(new ValueName.Behavior("billing", "settle"));

        assertEquals(Optional.of(List.of("line", "paid")), namesOf(settle.signature()));
        assertEquals(List.of("l", "amount"),
                assertInstanceOf(CheckedImplementation.Body.class, settle.implementation())
                        .parameters().stream().map(Core.Binder::name).toList());
    }

    @Test
    void aBehaviorWithNoBodyStillSaysTheNamesItDeclares() {
        BehaviorTarget rateFor = CheckedProgram.of(List.of(BILLING))
                .behavior(new ValueName.Behavior("billing", "rateFor"));

        assertInstanceOf(CheckedImplementation.Injected.class, rateFor.implementation());
        assertEquals(Optional.of(List.of("of")), namesOf(rateFor.signature()));
    }

    @Test
    void aSignatureThatDeclaresNoParametersNamesNone() {
        CheckedSignature now = CheckedProgram.of(List.of(BILLING))
                .behavior(new ValueName.Behavior("billing", "now")).signature();

        assertEquals(Optional.of(List.of()), namesOf(now));
    }

    @Test
    void aCompositionTakesInputsItDeclaresNoParametersFor() {
        CheckedSignature composed = CheckedProgram.of(List.of(BILLING))
                .behavior(new ValueName.Behavior("billing", "settledTwice")).signature();

        assertEquals(2, composed.inputs().size(), () -> "it takes what `settle` takes: " + composed);
        assertEquals(Optional.empty(), composed.declaredParameters());
    }

    @Test
    void eachParameterIsTheInputItStandsFor() {
        CheckedSignature settle = CheckedProgram.of(List.of(BILLING))
                .behavior(new ValueName.Behavior("billing", "settle")).signature();

        assertEquals(settle.inputs(), settle.declaredParameters().orElseThrow().stream()
                .map(CheckedSignature.Parameter::input).toList());
    }

    @Test
    void aBehaviorReadOffThePathSaysTheNamesItsModuleDeclares() {
        Map<String, ClassFileImage> published = Compiler.compile(PUBLISHED);
        CheckedProgram program = CheckedProgram.of(List.of(USES), ModulePath.of(published));

        assertEquals(Optional.of(List.of("of")), namesOf(
                program.behavior(new ValueName.Behavior("lib.rates", "spin")).signature()));
        assertEquals(Optional.of(List.of("item", "qty")), namesOf(
                program.behavior(new ValueName.Behavior("lib.rates", "quote")).signature()));
    }

    /** What another project published for a composition is the signature its stages computed, and
     *  not a declaration: its inputs arrive with no names, as they do where it was written. */
    @Test
    void aCompositionReadOffThePathDeclaresNoParameters() {
        Map<String, ClassFileImage> published = Compiler.compile(PUBLISHED);
        CheckedSignature composed = CheckedProgram.of(List.of(USES), ModulePath.of(published))
                .behavior(new ValueName.Behavior("lib.rates", "spunTwice")).signature();

        assertEquals(1, composed.inputs().size(), () -> "it takes what `spin` takes: " + composed);
        assertEquals(Optional.empty(), composed.declaredParameters());
    }

    private static Optional<List<String>> namesOf(CheckedSignature signature) {
        return signature.declaredParameters().map(parameters -> parameters.stream()
                .map(CheckedSignature.Parameter::name).toList());
    }
}
