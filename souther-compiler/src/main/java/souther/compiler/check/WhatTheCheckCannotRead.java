package souther.compiler.check;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.SourcePos;

/**
 * A limit this check is open about — the only thing an analysis that falls open may fall open on.
 *
 * <p>The check gives up on what it cannot read and the run-time check stands for what it gave up on,
 * which is what keeps a limit of this analysis from ever rejecting a valid program. What it must not
 * give up on is itself: a representation refusing to be built, a walk finding a state it says cannot
 * exist, a name read through nothing. Swallowed, those produce a subject with no findings, which is
 * exactly what a subject whose every construction is proven produces.
 *
 * <p><b>Which is why a limit is made and not recognised.</b> Read the other way round — every failure
 * a boundary meets is a limit unless it is one of the kinds listed there — the default is silence,
 * and a failure nobody has named yet is silently a limit. Nothing fails while that is true. Here the
 * default is the opposite: a limit exists because something that knew it was one said so, and a
 * failure with no such value behind it is not a limit and stops the compile.
 *
 * <p><b>Why there is no way in from a {@code Throwable}.</b> A factory taking one would let a
 * {@code catch} of everything become a limit again in a single line, and the census that counts who
 * may make one of these would go on reading the same number while it did. Every way in names what was
 * met, so a new one has to be written and read before a new kind of failure can be fallen open on.
 */
final class WhatTheCheckCannotRead {

    private final String said;

    private WhatTheCheckCannotRead(String said) {
        this.said = said;
    }

    /**
     * A call this reading has no signature for, which the expansion that produced the tree left
     * standing on purpose.
     *
     * <p>Both halves are required and neither is enough. That the expansion left it standing says
     * the tree is the one it meant to produce — a recursive helper is lowered to a method and its
     * call stays a call — and says nothing about who can read it. That this reading cannot name it
     * says only where the reading stops; a call left standing that the reader has a signature for is
     * read like any other, which is what a behavior's rule does with one. A call standing in a tree
     * no expansion named is neither, and is this compiler having failed to expand what it says it
     * expands: it goes on to the elaborator, which refuses it.
     */
    static WhatTheCheckCannotRead standingCallHasNoSignatureHere(String call, SourcePos at) {
        return new WhatTheCheckCannotRead("`" + call + "` is left standing by the expansion this"
                + " reads and this reading has no signature for it, at " + at);
    }

    /**
     * A clause the reading below the authoritative check could not type.
     *
     * <p>This typing is not the program's. The check that answers for a program has already read
     * every clause here and reported what is wrong with one; a refusal at this second reading says
     * only that this reading produced no term. For a program that check refuses, that is the same
     * mistake seen again and nothing more is owed for it. For a program it accepts, a refusal here
     * is a limit of this reading, which the run-time check stands for.
     */
    static WhatTheCheckCannotRead secondaryTypingDidNotFinish(CompileException why) {
        return new WhatTheCheckCannotRead(why.getMessage());
    }

    /** The same, of a clause whose meaning rests on a name that denotes nothing. */
    static WhatTheCheckCannotRead secondaryTypingDidNotFinish(Unanswerable why) {
        return new WhatTheCheckCannotRead(why.getMessage());
    }

    /**
     * A walk that ran to the end and left one of the answers it is written to produce unmade.
     *
     * <p>Its own limit rather than a failure: the walk borrows an analysis that is open about what it
     * reads, so a comparison it reached and settled nothing about leaves the obligation standing.
     */
    static WhatTheCheckCannotRead theWalkLeftAnAnswerUnmade(String said) {
        return new WhatTheCheckCannotRead(said);
    }

    /** What was met, for a reader that reports which limit this run came to. */
    String said() {
        return said;
    }

    @Override
    public String toString() {
        return said;
    }
}
