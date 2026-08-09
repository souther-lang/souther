package souther.compiler.diag.msg;

/**
 * The role of being said alongside the subject — a hint under it, or a label on a second place it
 * points at. What to write instead, or what the other place is.
 *
 * <p>Disjoint from {@link Reported} rather than a widening of it, and outside the {@link Message}
 * hierarchy for the reason given there. A sentence wanted in both roles is two records, the way a
 * wording that turns on a value is two records.
 */
public interface Supporting {
}
