package souther.compiler.execute;

/**
 * The questions the language can only answer by running the program.
 *
 * <p>Two of the things deciding whether Souther accepts a program need the program to run: a
 * constant construction has to satisfy the invariant of what it builds, and an {@code example} row
 * has to hold — in Souther a row that disagrees is a compile error and not a test failure. ADR-0032
 * settles how they are run: by the same program that will ship, with no second evaluator that could
 * disagree. That is not what this is about. This is about which way the dependency runs.
 *
 * <p>Acceptance asked those questions of the JVM. It reflected over a generated class name, built
 * class loaders, and handed an artifact of emitted classes to the thing that runs rows, so a caller
 * with nothing to do with the JVM went through it anyway and a program the JVM could not emit was
 * refused whether or not the language had anything against it. Asked here instead, the questions
 * are the language's and the JVM is one implementation of the answering.
 *
 * <p>What crosses, in both directions, is what the language asked and what happened. No
 * {@code Db}, no {@code Compilation}, no artifact of emitted classes, no class loader, no generated
 * class, and no bare {@code Object} value — in what this is asked as well as in what it answers. A
 * capability asked in the machine's words is the same dependency with an interface in front of it;
 * that is what the walk over this boundary refuses, and refusing it in the answers alone would
 * leave half of it standing.
 *
 * <p>It does not say which implementation runs. ADR-0032 does, and today the answer is the
 * generated JVM program. If that is ever re-opened, what it takes is a second implementation of
 * this rather than taking the example subsystem apart; and if it never is, the arrangement still
 * reads correctly — the policy is then a statement about which implementation is used, rather than
 * a shape the whole subsystem is built into.
 */
public interface ProgramExecution {

    /**
     * Whether {@code written} satisfies the invariant of the type it builds.
     *
     * <p>Answered by running the check the compile has for that type, which is the check a
     * construction at run time would run. Where it cannot be run here the answer says so and the
     * run-time check stands.
     */
    ConstantOutcome check(ConstantConstruction written);
}
