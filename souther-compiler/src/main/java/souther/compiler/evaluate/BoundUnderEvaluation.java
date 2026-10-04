package souther.compiler.evaluate;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import souther.runtime.Lists;
import souther.runtime.Maps;
import souther.runtime.Representations;
import souther.runtime.Sets;
import souther.runtime.Strings;
import souther.runtime.TextAdmission;

/**
 * The runtime operations a class generated for evaluating binds as a function, each asking for the
 * evaluation's checkpoint when it is applied.
 *
 * <p>A decoder, an encoder and a crossing's canonicalization hand a runtime operation to something
 * that applies it later — Raoh's {@code map}, an element function a container is walked with — and
 * such a function may be made once and kept: a decoder held as a constant, an element encoder reused
 * for every member. A checkpoint captured when it was made would be the checkpoint of whichever
 * evaluation made it, and a later one applying it would spend that evaluation's budget. So the
 * function an evaluated class binds is one of these, which asks for the checkpoint each time it is
 * applied, as a counted point does, and hands it to the runtime's entry that takes one.
 *
 * <p>The compiler's and not the runtime's, for the reason {@link EvaluationContext} is: only a class
 * generated for evaluating names it, and a class that ships binds the runtime's own operation.
 */
public final class BoundUnderEvaluation {

    private BoundUnderEvaluation() {}

    public static TextAdmission admission(String text) {
        return Strings.admission(text, EvaluationContext.checkpoint());
    }

    public static String admit(String text) {
        return Strings.admit(text, EvaluationContext.checkpoint());
    }

    public static <T> Set<T> fromList(List<T> xs) {
        return Sets.fromList(xs, EvaluationContext.checkpoint());
    }

    public static <T> List<T> toList(Set<T> s) {
        return Sets.toList(s, EvaluationContext.checkpoint());
    }

    public static <T> List<Object> map(Function<? super T, Object> f, List<T> xs) {
        return Lists.map(f, xs, EvaluationContext.checkpoint());
    }

    public static Set<Object> map(Function<Object, Object> f, Set<?> s) {
        return Sets.map(f, s, EvaluationContext.checkpoint());
    }

    public static <K, V> Map<String, V> mapKeysWith(Function<K, ?> keyFn, Map<K, V> m) {
        return Maps.mapKeysWith(keyFn, m, EvaluationContext.checkpoint());
    }

    public static Map<Object, Object> canonicalizeWithCaptured(Function<Object, Object> keyFn,
                                                               Function<Object, Object> valueFn,
                                                               Map<Object, Object> m) {
        return Maps.canonicalizeWithCaptured(keyFn, valueFn, m, EvaluationContext.checkpoint());
    }

    public static Object sortedArray(Object encoded) {
        return Representations.sortedArray(encoded, EvaluationContext.checkpoint());
    }

    public static Object sortedObject(Object encoded) {
        return Representations.sortedObject(encoded, EvaluationContext.checkpoint());
    }

    public static BigDecimal canonicalNumber(BigDecimal amount) {
        return Representations.canonicalNumber(amount, EvaluationContext.checkpoint());
    }
}
