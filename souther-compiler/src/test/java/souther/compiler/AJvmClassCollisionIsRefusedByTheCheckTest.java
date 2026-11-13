package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A module whose classes the JVM cannot hold — two of its identities spelled as one class — is
 * refused by the check of the module, and not only where the classes are made. So what is asked
 * is the check's own answer, with nothing measured and no class made: one refusal, said once, and
 * a module that is neither observable nor shippable.
 */
class AJvmClassCollisionIsRefusedByTheCheckTest {

    private static final String A_BEHAVIOR_ON_A_DATA = """
            module probe

            data Quote = { subtotal: Int }

            behavior quote : (n: Int) -> Quote
                constructs Quote
            let quote (n) = Quote { subtotal = n }
            """;

    /** {@code source} held to be refused with {@code codes} by the check of the module. */
    private static void checkedAndRefusedWith(List<String> codes, String source) {
        ACompiledModel.refusedWith(codes, Compilation.ofSource(source, "Main"));
    }

    @Test
    void aBehaviorCapitalizedOntoADataIsSaidOnce() {
        checkedAndRefusedWith(List.of("E2105"), A_BEHAVIOR_ON_A_DATA);
    }

    @Test
    void twoBehaviorsCapitalizedOntoOneClassAreSaidOnce() {
        // `Run` is a name a behavior does not take on its own account, which is said as well.
        checkedAndRefusedWith(List.of("E2105", "E1006", "E1006"), """
                module probe

                data N = Int

                behavior run : (n: N) -> N
                    constructs N
                let run (n) = n
                behavior Run : (n: N) -> N
                    constructs N
                let Run (n) = n
                """);
    }

    @Test
    void aResultUnionCapitalizedOntoADataIsSaidOnce() {
        checkedAndRefusedWith(List.of("E2105"), """
                module probe

                data Req = { n: Int }
                data Ok = { v: Int }
                data NotFound
                data BillResult = { x: Int }

                behavior bill : (r: Req) -> Ok | NotFound
                    constructs Ok
                let bill (r) = if r.n > 0 then Ok { v = r.n } else NotFound
                """);
    }

    @Test
    void namesThatDoNotCollideAreToldNothingOfTheKind() {
        checkedAndRefusedWith(List.of(), """
                module probe

                data Quote = { subtotal: Int }

                behavior makeQuote : (n: Int) -> Quote
                    constructs Quote
                let makeQuote (n) = Quote { subtotal = n }
                """);
    }

    @Test
    void aModuleTheCheckRefusesIsNeitherObservableNorShippable() {
        Compilation compilation = Compilation.ofSource(A_BEHAVIOR_ON_A_DATA, "Main");
        assertFalse(compilation.db().ask(new Bodies.Observable("probe")).present(),
                "no program to run rows against");
        assertFalse(compilation.db().ask(new Bodies.Checked("probe")).present(), "and none to ship");
        ACompiledModel.refusedWith(List.of("E2105"), compilation);
    }

    /** A measure asks the check as it asks everything it rests on, and is told the same. */
    @Test
    void aMeasureIsToldWhatTheCheckSays() {
        Compilation compilation = Compilation.ofSource(A_BEHAVIOR_ON_A_DATA, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.db().ask(new Adequacy.Coverage("probe"));
        ACompiledModel.refusedWith(List.of("E2105"), compilation);
    }
}
