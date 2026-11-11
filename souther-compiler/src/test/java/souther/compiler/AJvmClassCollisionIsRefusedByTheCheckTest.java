package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A module whose classes the JVM cannot hold — two of its identities spelled as one class — is
 * refused where the check says what is wrong with it, and not only where the classes are made. A
 * measure or a diagnosis asks for no classes, so what it is told of such a module is what the check
 * found: one refusal, said once, and no measurement of a module nothing could run.
 */
class AJvmClassCollisionIsRefusedByTheCheckTest {

    private static List<String> codesAfterMeasuring(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation.errors().stream().map(each -> String.valueOf(each.diagnostic().code()))
                .toList();
    }

    @Test
    void aBehaviorCapitalizedOntoADataIsSaidOnceByAMeasure() {
        assertEquals(List.of("E2105"), codesAfterMeasuring("""
                module probe

                data Quote = { subtotal: Int }

                behavior quote : (n: Int) -> Quote
                    constructs Quote
                let quote (n) = Quote { subtotal = n }
                """));
    }

    @Test
    void twoBehaviorsCapitalizedOntoOneClassAreSaidOnceByAMeasure() {
        // `Run` is a name a behavior does not take on its own account, which is said as well.
        assertEquals(1, codesAfterMeasuring("""
                module probe

                data N = Int

                behavior run : (n: N) -> N
                    constructs N
                let run (n) = n
                behavior Run : (n: N) -> N
                    constructs N
                let Run (n) = n
                """).stream().filter("E2105"::equals).count());
    }

    @Test
    void aResultUnionCapitalizedOntoADataIsSaidOnceByAMeasure() {
        assertEquals(List.of("E2105"), codesAfterMeasuring("""
                module probe

                data Req = { n: Int }
                data Ok = { v: Int }
                data NotFound
                data BillResult = { x: Int }

                behavior bill : (r: Req) -> Ok | NotFound
                    constructs Ok
                let bill (r) = if r.n > 0 then Ok { v = r.n } else NotFound
                """));
    }

    @Test
    void aModelWhoseNamesDoNotCollideIsToldNothingOfTheKind() {
        assertEquals(List.of(), codesAfterMeasuring("""
                module probe

                data Quote = { subtotal: Int }

                behavior makeQuote : (n: Int) -> Quote
                    constructs Quote
                let makeQuote (n) = Quote { subtotal = n }
                """));
    }

    @Test
    void theCollisionIsNoMeasurementOfTheModule() {
        Compilation compilation = Compilation.ofSource("""
                module probe

                data Quote = { subtotal: Int }

                behavior quote : (n: Int) -> Quote
                    constructs Quote
                let quote (n) = Quote { subtotal = n }
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        assertFalse(compilation.db().ask(new Bodies.Observable("probe")).present(),
                "a module the JVM cannot hold is no program to run rows against");
        assertFalse(compilation.db().ask(new Bodies.Checked("probe")).present(),
                "and none to ship");
    }
}
