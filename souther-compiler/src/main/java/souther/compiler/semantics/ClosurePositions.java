package souther.compiler.semantics;

/**
 * Where an operation's signature puts a closure and a container whose contents that closure could
 * be handed: the argument the closure is, the parameter of it a content would arrive on, the
 * argument the container is, and the parameter a map's key would arrive on.
 *
 * <p>Read off types, and so about places and nothing else. That the operation hands its closure
 * anything at all is not a type's to say ({@link Combinator}).
 *
 * @param keyParam the closure parameter a key would arrive on, or {@link Combinator#NO_KEY}
 */
public record ClosurePositions(int closureArg, int elementParam, int containerArg, int keyParam) {}
