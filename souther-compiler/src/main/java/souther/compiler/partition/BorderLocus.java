package souther.compiler.partition;

import souther.compiler.diag.Citation;

/**
 * Where a reader is sent to see the line a row is owed at.
 *
 * <p>Two ways and no third, because a rule is found one of two ways: a comparison is written at a
 * place in a body and a reader is pointed at it; a clause is called something and a reader is told
 * the name. Which of the two a rule is, the rule itself answers
 * ({@link OriginRef#isWrittenRatherThanNamed}), so nothing here decides it and no reader has to.
 *
 * <p><b>Beside whose the row is, and not derived from it.</b> Who owes a row here is what settled
 * the point ({@link PointAttribution}); where to look at the line is what drew it. The two agree
 * today — a body's comparison is written and a declaration's clause is named — and they are two
 * questions all the same: a generated declaration with a place in a source, or a clause a body
 * narrowed, moves one without moving the other. Read one off the other, that day arrives as a
 * reader pointed at nothing or told a name that names no rule.
 *
 * <p><b>And not the origin.</b> {@link OriginRef} says which reading of the rule drew this line —
 * a comparison inside a helper carries the call it was read through — and a point read at two
 * positions has as many of those as it has readings. What a reader is shown is the same at all of
 * them, which is what makes this the part a point can hold.
 */
public sealed interface BorderLocus {

    /** The line is written here, and a reader is pointed at it. */
    record WrittenAt(Citation at) implements BorderLocus {

        public WrittenAt {
            if (at == null) {
                throw new IllegalArgumentException("a line written somewhere is written somewhere");
            }
        }
    }

    /**
     * The line is called this, and a reader is told the name.
     *
     * <p>The rule's own name and never a place a body reached it at: a clause is read wherever the
     * type is carried, and the name is what does not move between those.
     */
    record NamedBy(String named) implements BorderLocus {

        public NamedBy {
            if (named == null || named.isEmpty()) {
                throw new IllegalArgumentException("a line found by its name has one");
            }
        }
    }

    /** How a reader finds the line {@code origin} drew. */
    static BorderLocus of(OriginRef origin) {
        return origin.isWrittenRatherThanNamed()
                // A rule found by where it is written has a place, which is what the same answer
                // says. A rule that answered one and not the other would be found neither way.
                ? new WrittenAt(origin.citation().orElseThrow(() -> new IllegalStateException(
                        "`" + origin.named() + "` is found by where it is written and is nowhere")))
                : new NamedBy(origin.named());
    }
}
