package souther.compiler.fmt;

/**
 * A place the layout may break, the group whose decision settles it, and what the layout wrote
 * there.
 *
 * <p>It is here whether or not a break was written. Where the canonical form keeps a line whole
 * there is no break to point at, and a source that broke there has still departed from the group's
 * decision — so what a source gap is matched against is the opportunity rather than what the layout
 * realized.
 *
 * <p>{@code at} is where in the text it stands: the offset the break was written at, or the offset
 * the flat form was written at where none was. Without it an opportunity the layout did not take is
 * somewhere in the document and nowhere in the output, and matching a source gap against it would
 * mean laying the document out again to find out where it would have been.
 */
record Opportunity(Doc.LineRef line, Doc.GroupRef settledBy, boolean broke, int at) {
}
