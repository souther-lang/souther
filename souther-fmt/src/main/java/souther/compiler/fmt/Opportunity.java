package souther.compiler.fmt;

/**
 * A place the layout may break, the group whose decision settles it, and what the layout wrote
 * there.
 *
 * <p>It is here whether or not a break was written. Where the canonical form keeps a line whole
 * there is no break to point at, and a source that broke there has still departed from the group's
 * decision — so what a source gap is matched against is the opportunity rather than what the layout
 * realized.
 */
record Opportunity(Doc.LineRef line, Doc.GroupRef settledBy, boolean broke) {
}
