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
 * <p>Not a verdict about the position. Whether it comes back divided is settled elsewhere and by
 * other evidence: a rule a body writes may divide a position whose own type this could not read
 * into. What is here is what this reading was short of, which is true either way and is what an
 * author is told so that a report does not print an absence it did not establish.
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
