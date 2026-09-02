package souther.compiler.report;

/**
 * What a document calls one thing keeping an adequacy verdict open.
 *
 * <p>An enum for the reason {@link WeakeningWord} is one, which is the reason every enumerated
 * field of this report has one: the shipped schema names these words in its own file and is held
 * against this, so a word added here has to be taught to the schema before it can be written.
 * Written as string literals in the renderer instead, the two spellings were kept in step by hand
 * and nothing stopped either of them moving alone.
 *
 * <p>Not one constant per {@link AdequacyOpening} arm, and not a word for every arm either. An
 * opening that is a measure going without something writes the word that measure's weakening
 * already has, because that vocabulary exists and a second spelling of it would be a second thing
 * to keep in step. What is here is everything else — the ways a verdict stays open that no
 * weakening covers.
 *
 * <p>So one arm may write more than one of these. A showing that was stopped says which stopped it,
 * because an observation that did not come back and a composing this compiler declined to do are
 * different news and answer differently about a wider run.
 */
public enum AdequacyOpeningWord {

    /** A measure the verdict rests on was never made, so a gap it could have found is one nobody
     *  looked for. What it was waiting for is said beside it. */
    NOT_MEASURED,

    /** The rows are read out, no row is at a point the model owes one at, and what was read to show
     *  a row can be written there did not come back. */
    SHOWING_STOPPED,

    /** The same point, where this compiler declined to compose a candidate for it at all. Its own
     *  word beside the one above, because a figure of its own decided it. */
    NOTHING_WAS_COMPOSED,

    /** And the same point again, where nothing was stopped and nothing arrived: no showing was
     *  made, so there is no limit to raise and nothing to name. */
    NOTHING_SHOWED_IT
}
