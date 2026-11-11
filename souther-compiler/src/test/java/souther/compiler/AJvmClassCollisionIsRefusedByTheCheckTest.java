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

    /** What the check of {@code source} says, by code. */
    private static List<String> codesOfTheCheck(Compilation compilation) {
        compilation.db().ask(new Bodies.ModuleCheck("probe"));
        return compilation.errors().stream().map(each -> String.valueOf(each.diagnostic().code()))
                .toList();
    }

    @Test
    void aBehaviorCapitalizedOntoADataIsSaidOnce() {
        assertEquals(List.of("E2105"),
                codesOfTheCheck(Compilation.ofSource(A_BEHAVIOR_ON_A_DATA, "Main")));
    }

    @Test
    void twoBehaviorsCapitalizedOntoOneClassAreSaidOnce() {
        // `Run` is a name a behavior does not take on its own account, which is said as well.
        assertEquals(1, codesOfTheCheck(Compilation.ofSource("""
                module probe

                data N = Int

                behavior run : (n: N) -> N
                    constructs N
                let run (n) = n
                behavior Run : (n: N) -> N
                    constructs N
                let Run (n) = n
                """, "Main")).stream().filter("E2105"::equals).count());
    }

    @Test
    void aResultUnionCapitalizedOntoADataIsSaidOnce() {
        assertEquals(List.of("E2105"), codesOfTheCheck(Compilation.ofSource("""
                module probe

                data Req = { n: Int }
                data Ok = { v: Int }
                data NotFound
                data BillResult = { x: Int }

                behavior bill : (r: Req) -> Ok | NotFound
                    constructs Ok
                let bill (r) = if r.n > 0 then Ok { v = r.n } else NotFound
                """, "Main")));
    }

    @Test
    void namesThatDoNotCollideAreToldNothingOfTheKind() {
        assertEquals(List.of(), codesOfTheCheck(Compilation.ofSource("""
                module probe

                data Quote = { subtotal: Int }

                behavior makeQuote : (n: Int) -> Quote
                    constructs Quote
                let makeQuote (n) = Quote { subtotal = n }
                """, "Main")));
    }

    @Test
    void aModuleTheCheckRefusesIsNeitherObservableNorShippable() {
        Compilation compilation = Compilation.ofSource(A_BEHAVIOR_ON_A_DATA, "Main");
        assertFalse(compilation.db().ask(new Bodies.Observable("probe")).present(),
                "no program to run rows against");
        assertFalse(compilation.db().ask(new Bodies.Checked("probe")).present(), "and none to ship");
    }

    /** A measure asks the check as it asks everything it rests on, and is told the same. */
    @Test
    void aMeasureIsToldWhatTheCheckSays() {
        Compilation compilation = Compilation.ofSource(A_BEHAVIOR_ON_A_DATA, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.db().ask(new Adequacy.Coverage("probe"));
        assertEquals(List.of("E2105"), compilation.errors().stream()
                .map(each -> String.valueOf(each.diagnostic().code())).toList());
    }
}
