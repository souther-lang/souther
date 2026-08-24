package souther.compiler.semantics;

/**
 * Which argument of an operation is the closure it applies, which parameter of that closure the
 * value arrives on, and which argument holds the values it comes from.
 *
 * <p>Three numbers about one operation, which is what "hands its closure the contents of" comes to
 * when it is said in argument positions. It is a description of the operation and belongs here; how
 * it is arrived at — reading the library's own signature — is the frontend's and belongs there
 * ({@link souther.compiler.check.Combinators}).
 *
 * <p>The numbers are positions of the operation's arguments, so one is meaningful only beside a
 * call to that operation. Nothing here reads them; they are read where an {@link ArgumentRef} is
 * resolved.
 */
public record Combinator(int closureArg, int elementParam, int containerArg) {}
