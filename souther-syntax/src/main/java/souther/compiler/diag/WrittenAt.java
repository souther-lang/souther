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
     * <p>Takes the coordinate and not a {@link SourceRef} over it. A reference holds a source of its
     * own beside the one the coordinate carries, and the two can disagree — a walk over one module
     * pairs its own source with a position from a helper another module of the same compile wrote.
     * Reading either of them was survivable while each reader picked one; a citation is the single
     * answer about a place, so a contradiction inside it is a place that is two places.
     */
    abstract Citation cite(SourcePos reachedFrom);

    /** The ordinary answer: what every coordinate a source was read for carries. */
    public static final WrittenAt HERE = new AtItsPlace();

    /**
     * The provenance of a copy that could not keep the positions it was written at.
     *
     * <p>Minted here and nowhere a source is read: a coordinate a parser made is where the code is,
     * by construction, and one that says otherwise was made by a pass that put code somewhere it was
     * not written.
     *
     * @param declaration the name a reader here reaches that code by: {@code helpers.atLeastZero},
     *        {@code List.map}. How it is reached and not which module declares it — a name reached
     *        from out of sight is qualified, so it is already enough to look the code up by, and the
     *        declaring module is a second value a report would have to show and has nothing to add
     *        ({@code List.map} is declared in {@code souther.list}, which is not how anyone reaches
     *        it). Where the code out of sight is a whole module rather than something in one, the
     *        module's name is how it is reached — {@code lib.text} is what a reader here imports —
     *        and the two answers coincide
     */
    public static WrittenAt outOfSight(String declaration) {
        return new StoodInFor(declaration);
    }
}
