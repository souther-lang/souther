package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Every call of {@link ACompiledModel} that hands a model back stops the test for a model that
 * does not compile, or that is not refused as the test said.
 *
 * <p>{@code ATestThatReadsAModelsReportAsksThatTheModelCompilesTest} takes a model such a call
 * hands back to have been asked about, and lists the calls by name. That is true of a call only if
 * it stops for a model that does not hold, which is held here for each, so that a call is on that
 * list with a test that says what it does, and a call that hands a model back without stopping
 * is one the list does not take.
 */
class ACompiledModelHoldsAModelToCompilingTest {

    private static final String SOUND = """
            module sound

            let one = 1
            """;

    private static final String BROKEN = """
            module broken

            let x = missing
            """;

    private static Compilation sound() {
        return Compilation.ofSource(SOUND, "Main");
    }

    private static Compilation broken() {
        return Compilation.ofSource(BROKEN, "Main");
    }

    @Test
    void compilesStopsForAModelWithAnError() {
        assertDoesNotThrow(() -> ACompiledModel.compiles(sound()));
        assertThrows(AssertionError.class, () -> ACompiledModel.compiles(broken()));
    }

    @Test
    void answeredStopsForASourceWithAnError() {
        assertDoesNotThrow(() -> ACompiledModel.answered(SOUND));
        assertThrows(AssertionError.class, () -> ACompiledModel.answered(BROKEN));
    }

    @Test
    void measuredStopsForASourceWithAnError() {
        assertDoesNotThrow(() -> ACompiledModel.measured(SOUND,
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS)));
        assertThrows(AssertionError.class, () -> ACompiledModel.measured(BROKEN,
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS)));
    }

    @Test
    void refusedWithStopsForAModelThatIsNotRefusedAsSaid() {
        assertDoesNotThrow(() -> ACompiledModel.refusedWith(List.of(), sound()));
        assertThrows(AssertionError.class, () -> ACompiledModel.refusedWith(List.of(), broken()));
        assertThrows(AssertionError.class,
                () -> ACompiledModel.refusedWith(List.of("E1023"), sound()));
    }

    @Test
    void refusedOnlyWithStopsForAnErrorOutsideWhatWasSaid() {
        assertDoesNotThrow(() -> ACompiledModel.refusedOnlyWith(Set.of(), sound()));
        assertThrows(AssertionError.class,
                () -> ACompiledModel.refusedOnlyWith(Set.of(), broken()));
    }

    @Test
    void sharedStopsForAModelThatIsNotAsSaidEveryTimeItIsGivenOut() {
        ACompiledModel.Shared shared = new ACompiledModel.Shared();
        try {
            assertDoesNotThrow(() -> shared.compiles("sound", ACompiledModelHoldsAModelToCompilingTest::sound));
            assertThrows(AssertionError.class,
                    () -> shared.compiles("broken", ACompiledModelHoldsAModelToCompilingTest::broken));
            assertThrows(AssertionError.class, () -> shared.refusedWith(List.of(), "other",
                    ACompiledModelHoldsAModelToCompilingTest::broken));
        } finally {
            shared.release();
        }
    }
}
