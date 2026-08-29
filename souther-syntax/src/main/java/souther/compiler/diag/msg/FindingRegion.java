package souther.compiler.diag.msg;

/**
 * A label whose region is itself part of what the diagnostic finds wrong, rather than something
 * pointed at so that a reader can see why the primary is.
 *
 * <p>The question is not whether a reader has to look there. It is whether the diagnostic passes
 * judgment on it. Nearly every report is decided by reading something written somewhere else — a
 * declaration, a rule, a signature, a definition — and showing a reader that text is what a second
 * region is ordinarily for. Being the premise a judgment was made under is not being judged.
 *
 * <p>So a report of the form <em>subject judged against reference</em> has one place it is written,
 * whatever it points at: a value refused by an invariant, a call that does not match a declaration,
 * a body that does not meet what it implements. The subject is where the problem is; the reference
 * is what decided it, and marking it would assert something about a line the diagnostic says
 * nothing about — a line whose author, where the reference is a library's, has nothing to do.
 *
 * <p>What this is for is the other shape, where no region is the premise the others are measured
 * by. Two statements that contradict, neither of which the model is to be held to over the other.
 * The two ends of a relation that may not exist at all, where what is wrong is that they are
 * connected: an invariant clause reaching a construction is refused for the reaching, so the clause
 * and the construction are both part of it. There the problem is not readable from any one of them,
 * and it is written at each.
 *
 * <p>Not a claim about whose fault it is, and not about whether the file can be edited. Those come
 * apart from this — the author of a clause a construction fails may have written nothing wrong and
 * may own both files — and deciding on them is how a rule ends up about people rather than about
 * what a report says.
 *
 * <p>A role of the record and not of the place it is used at, which is what {@link Supporting}
 * already asks of a wording: a sentence wanted in both roles is two records. So a wording cannot be
 * one of these at one site and a premise at another, and there is nowhere to write the second
 * answer.
 */
public interface FindingRegion extends Supporting {
}
