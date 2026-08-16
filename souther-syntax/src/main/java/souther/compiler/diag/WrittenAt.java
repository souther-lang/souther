package souther.compiler.diag;

/**
 * Whether a coordinate is where the code it names is written, or stands in for code written
 * somewhere this compile cannot show.
 *
 * <p>A body is spliced into everything that calls it, and a copy is read against the caller's file.
 * Where the copy came from a source this compile holds, the copy keeps the positions it was written
 * at and there is nothing to say: the coordinate is the place. Where it came from one this compile
 * has no source for — the standard library, a module read back off the module path — those positions
 * name a file nobody holds, so the copy is given the call site instead. That coordinate is a place
 * in the caller's file, and it is not where the code is.
 *
 * <p>Both facts have to travel, because a report needs both and cannot work either out from the
 * other. Where the caret goes is the coordinate; whether the caret is at the code is this. A
 * coordinate that carried only the first says a construction is at a call that constructs nothing —
 * which is what {@code E2011} said of {@code mk(n)}, in those words, before this existed.
 *
 * <p>It travels on the coordinate rather than on the node because the coordinate is what every pass
 * already carries. A slot beside it would be one more thing each of the places that rebuilds a node
 * has to pass on, and a rebuild that passed the wrong one would compile — which is the shape of
 * defect this is here to close, written a second time.
 *
 * <p>This is what a pass writes down, and it is not what a report says. The two are different
 * questions and this answers only the first, so what it publishes is whether the coordinate stands
 * in ({@link #isOutOfSight()}) and nothing else: no reader can take the declaration out of it and
 * write a place of its own. Turning it into something a report may say is {@link #cite}, which is
 * package-private and reached through {@link Citation#of}. Every statement about where code is
 * written is then a {@link Citation}, whose two cases a reader has to tell apart to read either.
 *
 * <p>A class rather than an interface for the same reason. An interface's methods are public, so a
 * projection declared on one would be a projection anybody could call, and the arms would have to
 * carry public accessors for the values it reads. Being a class puts the projection where only this
 * package can reach it and leaves the arms nothing to expose.
 *
 * <p>Two states, and a reader must say which it means: reading it off a null would put "the code is
 * here" and "nobody said" under one answer.
 *
 * <h2>What this answers, and what it must never be asked</h2>
 *
 * <p>This is <b>authored-source provenance as a report can observe it</b>, and it is not where a
 * parser's cursor was. A module read back off the module path is parsed from a text put back
 * together out of what the module published, and line 4 column 5 of that text exists — a parser
 * really did read a character there. It is still not {@link #HERE}: no reader holds a file those
 * numbers are of. Defining this as the parse buffer's position is locally true and is how the whole
 * defect reads as correct, so it is written down here instead of left to be worked out again.
 *
 * <p>Two rules hold over this type and over everything that carries one.
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
 * all — which is why dropping second regions naming no source was withdrawn from #756.
 *
 * <p>The second is why {@link SourcePos#sourceId()} is a separate component and is not read off
 * this, nor this off it. The two are orthogonal, and a body copied from out of sight is the witness:
 * it is out of sight and in a source of this compile at once, because the splice gave it the
 * caller's place to be read against. A shortcut in either direction — a null source taken to mean
 * out of sight, a synthesized node taken to mean the diagnostic's own file — puts the two back under
 * one answer, which is the shape this exists to close.
 */
public sealed abstract class WrittenAt permits AtItsPlace, StoodInFor {

    WrittenAt() {
    }

    /** Whether the coordinate carrying this stands in for code written somewhere this compile
     *  cannot show. The whole of what a pass outside this package is told: what it stands in for is
     *  a statement about a place, and statements about places are {@link Citation}s. */
    public abstract boolean isOutOfSight();

    /**
     * This provenance as something a report may say about {@code reachedFrom}.
     *
     * <p>The one way the declaration a coordinate stands in for reaches a reader, and package-private
     * so that it stays the one way. Every surface that says where code is written — the terminal, the
     * JSON a build reads, an editor, the adequacy report — reads a {@link Citation}, and a surface
     * added later has nothing else to read: there is no accessor here to build a second answer out
     * of.
     *
     * <p>Total, and defined on both arms. A projection that answered only for the case it was written
     * for would leave the other reading the coordinate, which is where this started.
     *
     * <p>Takes the coordinate, and what it answers with carries that coordinate and nothing beside
     * it. A source held next to one a coordinate already carries can disagree with it — a walk over
     * one module pairs its own source with a position from a helper another module of the same
     * compile wrote. Reading either of them was survivable while each reader picked one; a citation
     * is the single answer about a place, so a contradiction inside it is a place that is two
     * places.
     */
    abstract Citation cite(SourcePos reachedFrom);

    /**
     * The same provenance, reached by {@code name} — what a splice writes when it learns the name
     * the call reaches, a parse of a published module having known only the module.
     *
     * <p>A refinement of one authority's answer and not a second answer: what kind of thing this
     * compile is without is kept, and only the name a reader here writes for it is replaced. So the
     * pass that copies a body never decides whether the body is out of sight — it reads that — and
     * says only the one thing it is the first to know.
     *
     * @throws IllegalStateException where the code is written at its place. There is no name to
     *         reach code by that is where a reader already is, and a caller that got here with
     *         {@link #HERE} was branching on something other than the question
     */
    public abstract WrittenAt reachedBy(String name);

    /** The ordinary answer: what every coordinate read off a file this compile holds carries. */
    public static final WrittenAt HERE = new AtItsPlace();

    /**
     * The provenance of code this compile has no file for.
     *
     * <p>Minted where a text is turned into positions, and nowhere downstream of that. A coordinate
     * made from a file this compile holds is where the code is, by construction; one made from a
     * text reassembled out of what a module published is not, by construction; and both are settled
     * by the caller that knows which text it handed over. A pass that decided it later would be the
     * second authority the rules above forbid.
     */
    public static WrittenAt outOfSight(SourceProvenance provenance) {
        return new StoodInFor(provenance);
    }
}
