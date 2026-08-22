package souther.compiler.fmt;

/**
 * What the layout did with one group, and the display column it was measured from.
 *
 * <p>A column and not an index into the text, since the width it was measured against is a screen
 * width. The column the width read, which past a table's column is not the column the group stands
 * at on the screen: padding is not content the width has to make room for, so it is not in this
 * number, and a reader looking for where the group was written finds that in the layout's text
 * rather than here.
 *
 * <p>The group is named by its own identity rather than by its shape. Two groups written the same
 * way are two decisions, and the conditional-layout rule answers about a group rather than about a
 * kind of group.
 */
record GroupDecision(Doc.GroupRef group, int startColumn, Outcome outcome) {
}
