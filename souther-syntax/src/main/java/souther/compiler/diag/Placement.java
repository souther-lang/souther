package souther.compiler.diag;

import souther.compiler.source.SourceId;

import java.util.Objects;

/**
 * Which text a position is in, and what this compilation knows about that text.
 *
 * <p>Two questions, and this is their product. Whether this compilation can show a reader the text —
 * whether it holds a file and can name it — and whether the code the position names is written at
 * the position or somewhere this compilation has no file for. Neither is read off the other. A body
 * copied out of a published module is the witness: it is written out of sight and it is in a source
 * of this compile at once, because the splice gave it the caller's place to be read against.
 *
 * <blockquote>
 * <table>
 *   <caption>The states, as the quadrants of those two questions</caption>
 *   <tr><td></td><td>the code is written here</td><td>the code is written elsewhere</td></tr>
 *   <tr><td>named by this compile</td>
 *       <td>{@link #aFileOfThisCompile}</td><td>a splice, or a report moved to an import line</td></tr>
 *   <tr><td>not named</td>
 *       <td>{@link #aTextWithNoIdentity}</td><td>{@link #whatAModulePublished}</td></tr>
 * </table>
 * </blockquote>
 *
 * <p>Four arms because the two questions have two answers each, and not because four kinds of text
 * were counted. The difference matters the day a fifth arm is proposed: either it fills a quadrant
 * one of these already fills, in which case it is one of these written wrongly, or it cannot answer
 * one of the two questions, in which case whoever proposes it has found a third question and owes an
 * account of it. {@code TheStatesOfAPlacementAreTheQuadrantsOfTwoQuestionsTest} holds the arms to
 * that, so the derivation is a check rather than a paragraph somebody has to notice.
 *
 * <p>Held as one value because the pair is what is legal and the components are not. This was two
 * fields on {@link SourcePos} — a source identity that could be null and a separate answer about
 * where the code was written — which is nine combinations for four states, and every reader worked
 * the classification out again from whichever component it had: a null source read as "out of
 * sight" by one, as "the diagnostic's own file" by another, as "drop this" by two more. The rule
 * that only four pairs are legal already existed and was already written down, on the class that
 * made positions out of a parse; it just was not what a position held.
 *
 * <p>Two rules hold over this and over everything that carries one.
 *
 * <blockquote>
 * A source location has exactly one authority for its provenance.
 * <br>
 * The source in which coordinates are interpreted is never inferred from how the code came to
 * exist.
 * </blockquote>
 *
 * <p>The first is why this is minted where a text is turned into positions and nowhere else: a pass
 * that worked provenance out downstream would be a second authority, and the two disagree the day
 * one of them learns something the other does not. It is what {@code HelperInliner} used to do, by
 * comparing the declaring module with its own, and what a reader of finished reports cannot do at
 * all.
 *
 * <p>The second is why the two questions above stay two questions. A shortcut in either direction —
 * a text with no name taken to mean the code is elsewhere, a copied body taken to be in the file it
 * came from — puts them back under one answer, which is the shape this exists to close.
 *
 * <h2>What this publishes, and what it does not</h2>
 *
 * <p>Outside this package this is opaque: three ways to make one, a way to make a position out of
 * one, and a value to hand back to {@link SourcePos#standingInFor}. It answers no question. That is
 * deliberate — every question a reader has about a place is answered by exactly one projection, and
 * each of those lives here:
 *
 * <ul>
 *   <li>{@link Citation#of} — what a report may say about where the code is written.
 *   <li>{@link DiagnosticPlace#of} — where a reader may be sent.
 *   <li>{@link SourcePos#isOutOfSight()} — whether the position is where the code is, which is the
 *       second question on its own and is what sizes an underline.
 * </ul>
 *
 * <p>A pass that reads the arms would be a fourth answer to whichever of those questions it was
 * really asking, arrived at privately, and that is the defect this whole family is. So the two
 * questions are package-private methods rather than published predicates: something that answered
 * {@code namedByThisCompile()} to the world would be {@code sourceId() != null} again, under a name
 * that reads like an improvement.
 *
 * <p>A class rather than an interface for that reason. An interface's methods are public, so the
 * two questions could not be closed and the arms would have to carry public accessors for what they
 * hold.
 *
 * <p>Value equality, because {@link SourcePos} is compared by every pass that rebuilds a node, by the
 * incremental engine deciding whether an answer changed, and by the store deciding whether two
 * diagnostics are one problem. Two positions that differ here are read differently by every surface,
 * so an answer that changed only here has changed.
 *
 * <p>The provenance is in the equality and is not published. A caller may ask whether this is the
 * placement it already holds and may not ask what it is: reading the declaration off a position and
 * writing a place of one's own is how the same position came to be presented as where code is
 * written by three surfaces and qualified by one.
 */
public sealed abstract class Placement
        permits InAFileOfThisCompile, InAnUnnamedText, StandingInFor, InWhatAModulePublished {

    Placement() {
    }

    /**
     * Whether this compilation holds a file for the text, under an identity it can name.
     *
     * <p>The first of the two questions. Package-private, and it stays so: this is what a reader
     * needs to be sent anywhere, and a reader that could ask it would answer "may I quote this" and
     * "where is the code written" out of one boolean, which is what having it as a nullable source
     * identity did.
     */
    abstract boolean namedByThisCompile();

    /**
     * Whether the code this position names is written at the position.
     *
     * <p>The second of the two questions. False for a text put back together out of what a module
     * published, whose line 4 is a real line that no reader holds, and for a copy of such a body
     * that was given the caller's place to be read against.
     */
    abstract boolean codeIsWrittenHere();

    /** The source this compilation files the text under, or null where it names none. Read by
     *  {@link SourcePos} and by the projections in this package, and by nothing else: outside them
     *  its absence is not an answer to any question anybody has. */
    abstract SourceId sourceId();

    /**
     * Where the code is written, for an arm that says it is written elsewhere.
     *
     * @throws NotWrittenElsewhere where the code is written at the position. There is nothing to
     *         say about where such code came from, and a caller that got here was branching on
     *         something other than the question
     */
    abstract SourceProvenance codeIsWrittenIn();

    /**
     * The same text, with the code in it written in {@code provenance} instead.
     *
     * <p>The first question is kept and the second is replaced. What a splice does to the place it
     * splices into: the caller still holds the file, or still does not, and what is now written
     * there is the body that was copied in.
     *
     * <p>Takes the provenance and not a placement, so that whatever this one already said about
     * where its code came from cannot be composed with it. That is not an omission. A position
     * already standing in for a body is standing in for the copy this one is nested inside, and the
     * body a position belongs to is the innermost one it was copied out of — so the outer answer is
     * about something else and replacing it is the whole of what is meant.
     */
    abstract Placement withCodeWrittenIn(SourceProvenance provenance);

    /** This placement as something a report may say about {@code at}. The one way what a position
     *  stands in for reaches a reader, and package-private so that it stays the one way. */
    abstract Citation cite(SourcePos at);

    /**
     * This text, standing in for code written where {@code declaring} says.
     *
     * <p>What an expansion gives a copy it cannot give its own positions, and what moving a report's
     * caret gives the place it moved to. Not where a stand-in is first decided: that is settled where
     * a text becomes positions, by the caller that knows what the text was. What this does is carry
     * an answer already given to a text somewhere else.
     *
     * <p>Total over the four arms, because a body is spliced into whatever calls it and a call is in
     * whatever text its caller is in — including a text this compile cannot name, and including a
     * body already copied out of somewhere else. Both are reached today, and a splice that refused
     * either would be refusing an ordinary compile.
     *
     * @throws NotWrittenElsewhere where {@code declaring} says its code is written at it. Standing in
     *         for code written where the reader already is is not a thing to say
     */
    public final Placement standingInFor(Placement declaring) {
        return withCodeWrittenIn(declaring.codeIsWrittenIn());
    }

    /**
     * The same placement, the code in it reached by {@code name} — what a splice writes when it
     * learns the name the call reaches, a parse of a published module having known only the module.
     *
     * <p>A refinement of one authority's answer and not a second answer: what kind of thing this
     * compile is without is kept, and only the name a reader here writes for it is replaced.
     *
     * @throws NotWrittenElsewhere where the code is written at the position
     */
    final Placement reachedBy(String name) {
        return withCodeWrittenIn(codeIsWrittenIn().reachedBy(name));
    }

    /** The position of {@code line} and {@code column} in this text. */
    public final SourcePos at(int line, int column) {
        return new SourcePos(line, column, this);
    }

    /** A file this compile holds, under the identity it holds it by. Its positions are where the
     *  code is, and they say which file they are in. */
    public static Placement aFileOfThisCompile(SourceId sourceId) {
        return new InAFileOfThisCompile(
                Objects.requireNonNull(sourceId, "a file of this compile is named"));
    }

    /**
     * A text nobody has named — a buffer an editor is holding and has not saved, a snippet a caller
     * parsed to look at the tree, a document being read before the compile knows what to call it.
     *
     * <p>Its positions are where the code is: what was read is what somebody wrote. What they do not
     * say is which file, so nothing built from them reaches a reader on its own, and a report made
     * against one is a report the caller has to place.
     */
    public static Placement aTextWithNoIdentity() {
        return InAnUnnamedText.IT;
    }

    /**
     * A text put back together out of what a module published, which this compile has no file for.
     *
     * <p>The positions are real positions in that text and are not where a reader can be sent, so
     * they say so from the moment they are made. Everything downstream — a body spliced into a
     * caller, a clause a construction is judged against, a guard that drew a line — reads the answer
     * rather than working it out from the source being absent.
     *
     * <p>There is deliberately no way to say "reassembled, and here is its source id": a text put
     * back together out of what a module published is in no file, and a caller with a file for it is
     * reading a file.
     */
    public static Placement whatAModulePublished(SourceProvenance provenance) {
        return new InWhatAModulePublished(
                Objects.requireNonNull(provenance, "code out of sight came from somewhere"));
    }

    /**
     * A placement asked where its code came from when its code is written at it.
     *
     * <p>Marked, for the reason {@code DiagnosticPlace.NotAPlace} is: a caller that got here was
     * branching on something other than the question, and an analysis that falls open would swallow
     * an unmarked one and report a subject as having nothing wrong with it.
     */
    static final class NotWrittenElsewhere extends IllegalStateException
            implements TheCompilerDisagreesWithItself {

        private static final long serialVersionUID = 1L;

        NotWrittenElsewhere(Placement of) {
            super("the code this names is written at it, so there is nothing to say about where it"
                    + " came from: " + of);
        }
    }
}
