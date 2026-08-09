package souther.compiler.diag.msg;

/**
 * A message said alongside the subject — a hint under it, or a label on a second place it points
 * at. What to write instead, or what the other place is.
 *
 * <p>Disjoint from {@link Reported} rather than a widening of it, because the two roles are what
 * tells a diagnostic's code apart from the sentences around it. A message that could be either
 * would be built as a hint while the build counted its code among the rules something reports, so
 * a rule whose subjects had all moved to another number would go on looking reported by the repair
 * written under it. A sentence wanted in both roles is two records, the way a wording that turns on
 * a value is two records.
 */
public non-sealed interface Supporting extends Message {
}
