package souther.compiler.diag.msg;

/**
 * A message that reports a rule — what a diagnostic is about, as opposed to what to write instead.
 *
 * <p>Only these carry a {@link Code}, and only these can be a diagnostic's subject: {@code say}
 * takes one and a hint or a secondary label takes any {@link Message}. The distinction is here
 * rather than in a convention because a diagnostic's code comes from its subject and from nothing
 * else. A hint carrying a code carries one nothing reads, and the build, counting the codes that
 * something reports, would count that one — so a rule whose sites had all moved to another number
 * would go on looking reported by the repair written under it.
 */
public non-sealed interface Reported extends Message {
}
