package souther.compiler.examples;

/**
 * The declarations of the compile whose rows are being run: the answer is of the module being
 * evaluated because it is of this compile of it.
 *
 * <p>Not public, and that is what it is for. This is not a description an answer gives of itself —
 * it is what excuses an answer from being held against the module the rows are written for, and an
 * answer that could name it could excuse itself by writing one word. Something supplied from outside
 * a compile is written outside this package, so the only origin it can state is one that carries its
 * declarations to be read.
 *
 * <p>The other half of the same defence is that {@link Answerer.Answer.Something#origin} is abstract:
 * that keeps the question from being left unanswered, this keeps it from being answered falsely.
 */
record TheCompilesOwn() implements Origin {}
