package souther.compiler.fmt;

/**
 * What the layout did with one group, and the column it was measured from.
 *
 * <p>The group is named by its own identity rather than by its shape. Two groups written the same
 * way are two decisions, and the conditional-layout rule answers about a group rather than about a
 * kind of group.
 */
public record GroupDecision(Doc.GroupRef group, int startColumn, Outcome outcome) {
}
