package souther.compiler.fmt;

/**
 * What the layout did with one group, and the display column it was measured from — the column on
 * the screen, not an index into the text, since the width it was measured against is a screen
 * width.
 *
 * <p>The group is named by its own identity rather than by its shape. Two groups written the same
 * way are two decisions, and the conditional-layout rule answers about a group rather than about a
 * kind of group.
 */
record GroupDecision(Doc.GroupRef group, int startColumn, Outcome outcome) {
}
