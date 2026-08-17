package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A fork standing in a {@code match}'s scrutinee is read once, and what was answered about it stays
 * answered.
 *
 * <p>A {@code Match}'s children are its scrutinee as well as its arm bodies, so a walk that reads
 * the scrutinee itself and then hands the node to the generic walk reads it twice — the second time
 * from under the fork, which is a place where something does stand above. The second answer
 * overwrites the first, and a claim that had been refuted comes back as one nothing settled.
 *
 * <p>Measured through the diagnostic rather than through the answers, because that is what an
 * author loses: the model below declares a case its own signature admits, and the compile has to
 * refuse it.
 */
class AForkInAScrutineeIsReadOnceTest {

    /**
     * The inner {@code match} is the first thing this body does, so reaching it is being applied at
     * all — and {@code Off} is a case the signature admits.
     */
    private static final String IN_A_SCRUTINEE = """
            module demo

            data On
            data Off
            data Perhaps
            data Flag = On | Off | Perhaps
            data Yes
            data Nope
            data Answer = Int

            behavior pick : (f: Flag) -> Answer
                constructs Answer, Yes, Nope

            let pick (f) = match (match f with
                    | On      -> Yes
                    | Perhaps -> Nope
                    | Off     -> unreachable "a Flag is never Off") with
                | Yes  -> Answer(1)
                | Nope -> Answer(0)
            """;

    /** The same claim where the rules do refuse the case, which must stay accepted. */
    private static final String REFUSED_FOR_REAL = """
            module demo

            data On
            data Off
            data Perhaps
            data Flag = On | Off | Perhaps
            data Live = Flag invariant value /= Off
            data Yes
            data Nope
            data Answer = Int

            behavior pick : (l: Live) -> Answer
                constructs Answer, Yes, Nope

            let pick (l) = match (match l.value with
                    | On      -> Yes
                    | Perhaps -> Nope
                    | Off     -> unreachable "a Live is never Off") with
                | Yes  -> Answer(1)
                | Nope -> Answer(0)
            """;

    @Test
    void aClaimInAScrutineeIsStillRefuted() {
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compileWithWarnings(IN_A_SCRUTINEE),
                "`Off` arrives, and the fork it arrives at is what this body does first");
        assertEquals("E1326", refused.diagnostic().code());
    }

    @Test
    void andOneTheRulesRefuseIsBorneOut() {
        // The control. A reading that answered "nothing settled it" everywhere would pass the test
        // above by refusing nothing, and this is what tells the two apart: here the rules do refuse
        // `Off`, the claim says what they say, and nothing is reported.
        assertEquals(0, Compiler.compileWithWarnings(REFUSED_FOR_REAL).warnings().size(),
                "a claim the rules bear out is neither refused nor warned about");
    }
}
