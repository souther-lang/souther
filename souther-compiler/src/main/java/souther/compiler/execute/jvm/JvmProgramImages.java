package souther.compiler.execute.jvm;

/**
 * Where the JVM implementation gets the classes of the compile it is running.
 *
 * <p>Only this implementation's, and deliberately so. What a compile emitted is not a fact about a
 * Souther program, so it does not cross {@code ProgramExecution} in either direction; but the
 * implementation that runs the JVM program cannot make those classes itself either, because making
 * them is the compiler answering its own questions. This is the one seam between the two, and it is
 * named in the machine's words because both of its sides are the machine.
 *
 * <p>What crosses it is a loader and not the emitted set. A caller handed the classes would have to
 * decide how they are defined and what stands behind them, and that decision is the reason a value
 * built here and one built by the parent are the same type rather than two under one name.
 */
public interface JvmProgramImages {

    /**
     * The loader compile-time code of {@code module} runs against: this compilation's classes over
     * the ones the projects it depends on already built.
     *
     * <p>Null where this compile has no class set for the module. Nothing was emitted to run, which
     * is not a fault of the program being asked about — the caller answers that the question was
     * not decided here, and the check that runs when the program does still applies.
     */
    ClassLoader compileTimeLoader(String module);

    /**
     * The program this compilation evaluates {@code module} as, recording the arms where the
     * compilation measures them.
     *
     * <p>One for the compilation, and every reading of the module is of it: its rows, its tables,
     * the values a search builds and the rows a search tries. Which one is not the caller's to say.
     * A reading that named the uncounted-arms program while the rows ran on the recording one would
     * have the module generated twice, and the two programs differ only in calls that record and
     * do nothing when no run is recording.
     *
     * <p>Null where this compile could not make it. The rows are then not run, which is not a fault
     * of the model they are about — the caller says what that means for what it was asked.
     */
    JvmProgramImage evaluating(String module);
}
