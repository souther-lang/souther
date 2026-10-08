package souther.compiler.check;

import souther.compiler.semantics.SideAnswered;

/**
 * How an operation's answer comes out, as the element of what it walks that witnesses it, with the
 * arguments that law is about resolved against the operation's declaration.
 *
 * <p>What the answer comes out as {@code result} exactly where some element of {@code container},
 * handed to {@code closure}, makes the closure answer as {@code ofTheClosure}
 * ({@link souther.compiler.semantics.OperationFact.ResultHasAnElementWitness}).
 *
 * @param result       how the operation's answer comes out
 * @param ofTheClosure how a witness's answer comes out
 * @param container    the argument whose elements are the witnesses
 * @param closure      the argument each element is handed to
 */
public record ElementWitness(SideAnswered result, SideAnswered ofTheClosure,
                             DeclaredArgument container, DeclaredArgument closure) {}
