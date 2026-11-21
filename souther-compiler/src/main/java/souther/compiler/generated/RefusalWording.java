package souther.compiler.generated;

import souther.runtime.boundary.Path;
import souther.runtime.boundary.Refusal;
import souther.runtime.boundary.Refusals;

import java.util.Map;
import java.util.stream.Collectors;

/**
 * What a refusal says in this compiler's words: one English sentence about the value, without where
 * it is. A refusal carries no message (spec {@code [#what-a-refusal-says]}), so a reporter words it,
 * and this is the compiler's reporter — a fixture that does not fit its type, and a crossing an
 * example writes, are told with it.
 */
public final class RefusalWording {

    private RefusalWording() {}

    /** Each refusal at its path, in the order they were found: {@code path: sentence}, the path's
     *  segments joined by {@code .}, and the sentence alone at the root. */
    public static String detail(Refusals refusals) {
        return refusals.asList().stream()
                .map(r -> {
                    String at = r.path().segments().stream().map(Path.Segment::text)
                            .collect(Collectors.joining("."));
                    return at.isEmpty() ? says(r) : at + ": " + says(r);
                })
                .collect(Collectors.joining("; "));
    }

    /** The sentence one refusal says. */
    public static String says(Refusal refusal) {
        return switch (refusal) {
            case Refusal.Absent _ -> "is required";
            case Refusal.NotOfItsKind r -> r.reason();
            case Refusal.NotOneOfTheNames r -> "must be one of " + r.names();
            case Refusal.NotInItsForm r -> r.reason();
            case Refusal.OneKeyTwice _ -> "two keys are the same key once decoded";
            case Refusal.Constraint r -> constraint(r.name(), r.data());
            case Refusal.Clause r -> r.failure().toString();
        };
    }

    private static String constraint(String name, Map<String, Object> d) {
        return switch (name) {
            case "minLength" -> "must be at least " + d.get("min") + " characters";
            case "maxLength" -> "must be at most " + d.get("max") + " characters";
            case "length" -> "must be exactly " + d.get("length") + " characters";
            case "pattern" -> "must match " + d.get("pattern");
            case "min" -> "must be at least " + d.get("min");
            case "max" -> "must be at most " + d.get("max");
            case "positive" -> "must be positive";
            case "nonNegative" -> "must be non-negative";
            case "nonEmpty" -> "must not be empty";
            case "minSize" -> "must have at least " + d.get("min") + " elements";
            case "maxSize" -> "must have at most " + d.get("max") + " elements";
            case "size" -> "must have exactly " + d.get("size") + " elements";
            case "unique" -> "must not contain duplicates: " + d.get("duplicates");
            default -> "breaks " + name + " " + d;
        };
    }
}
