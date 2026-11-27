package souther.cli.backend;

/**
 * What a {@link FakeBackend} jar holds under the name of a class of the compiler: it answers the
 * question that class answers, with an answer no compiler gives.
 */
public final class ASecondDefinition {

    private ASecondDefinition() {}

    public static String compilerVersion() {
        return FakeBackend.THE_JARS_OWN_COMPILER;
    }
}
