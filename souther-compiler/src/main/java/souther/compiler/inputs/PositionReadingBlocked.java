package souther.compiler.inputs;

/**
 * A position whose reading stopped before it got to what is written about it.
 *
 * <p>The other half of {@link UnreadRule}, and told apart from it by which authority answers. There
 * a rule was read and could not be used, and the finding names it; here nothing about any one rule
 * is known â a depth, a shape this does not reach into, a type that could not be worked out, a
 * gathering that stopped â and what there is to say is the position and the limit. Carrying a rule
 * for one of these would be naming a rule nothing observed.
 *
 * <p>Made after the answer, and not by the reading that stopped. What a producer records is a
 * candidate — {@link StructuralInspection.Blocked}, or the account the reading of values gave of
 * itself — and a candidate becomes one of these exactly where neither the position's own
 * declarations nor a body's rules answered for it. That is settled in one place
 * ({@code PendingPosition.reportable}), which is why nothing outside constructs one: written where
 * the producer records it, every position holding an {@code Option} said its values are held
 * inside something this does not reach into, whether or not the reading of it came to anything.
 *
 * <p>Not a verdict either. Whether the position comes back divided is a separate answer from the
 * same pair of readings, and neither is read off the other: this says what an author is waiting on,
 * so that a report does not print an absence it did not establish.
 *
 * @param at  the position, spelled the way a report names it
 * @param why what would have to change before the reading could get there, in this compiler's own
 *            terms. Which word a report writes for it is {@link ReportedReason}'s
 */
public record PositionReadingBlocked(TermPath at, BlockReason.AboutThePosition why) {

    public PositionReadingBlocked {
        if (at == null || why == null) {
            throw new IllegalArgumentException("a reading stopped somewhere, and at something");
        }
    }
}
