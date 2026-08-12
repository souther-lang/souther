package souther.compiler.check;

import souther.compiler.types.Type;
import java.util.List;

/**
 * The input and success types of a required (injected) behavior, for typing an inline call to it.
 * An injected behavior may take several inputs, so {@code params} is a list (empty for
 * {@code () -> R}). Public so the backend can build the same view when it re-types a closure body.
 */
public record ReqSig(List<Type> params, Type success) {}
