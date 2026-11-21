package souther.compiler.check;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.TakenAs;

import java.util.Collections;
import java.util.EnumMap;
import java.util.Map;

/**
 * A rule the declarations state of the parts of one date as it stands that no range of one part
 * says ({@link DatePartsLeft}): {@code Date.month(value) + Date.day(value) <= 20}, or a part held
 * away from a number. The weighed parts and {@code constant} are held against nought as
 * {@code relation}.
 *
 * <p>Each part as the date stands and never moved: a part of the date a day on is a part of
 * another date.
 */
public record RuleOfDateParts(Map<TakenAs.DatePart, ExactRatio> weights, ExactRatio constant,
                              Rel relation) {

    public RuleOfDateParts {
        if (weights.isEmpty() || constant == null || relation == null) {
            throw new IllegalArgumentException("a rule of the parts of a date weighs some part of"
                    + " it against a constant");
        }
        weights = Collections.unmodifiableMap(new EnumMap<>(weights));
    }
}
