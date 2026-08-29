package souther.compiler.diag.msg;

/**
 * The role of being said alongside the subject — a hint under it, a label on a second place it
 * points at, or a statement the body carries about where the caret is. What to write instead, what
 * the other place is, or what this place stands in for.
 *
 * <p>Disjoint from {@link Reported} rather than a widening of it, and outside the {@link Message}
 * hierarchy for the reason given there. A sentence wanted in both roles is two records, the way a
 * wording that turns on a value is two records.
 */
public interface Supporting {
}
