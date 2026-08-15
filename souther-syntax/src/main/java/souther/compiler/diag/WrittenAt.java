package souther.compiler.diag;

import java.util.Objects;

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
 * <p>Two states, and a reader must say which it means: reading it off a null would put "the code is
 * here" and "nobody said" under one answer.
 */
public sealed interface WrittenAt {

    /** The code this coordinate names is written at it. */
    record Here() implements WrittenAt {}

    /**
     * The coordinate stands in for code written in {@code declaration}, which this compile has no
     * source for. It is where the code was reached from — the call the body was spliced into — and
     * not where the code is, so a report anchored on it says so rather than claiming the place.
     *
     * @param declaration the name a reader here reaches that code by: {@code helpers.atLeastZero},
     *        {@code List.map}. How it is reached and not which module declares it — a name reached
     *        from out of sight is qualified, so it is already enough to look the code up by, and the
     *        declaring module is a second value a report would have to show and has nothing to add
     *        ({@code List.map} is declared in {@code souther.list}, which is not how anyone reaches
     *        it)
     */
    record OutOfSight(String declaration) implements WrittenAt {

        public OutOfSight {
            Objects.requireNonNull(declaration, "code out of sight is reached by a name");
        }
    }

    /** The ordinary answer: what every coordinate a source was read for carries. */
    WrittenAt HERE = new Here();
}
