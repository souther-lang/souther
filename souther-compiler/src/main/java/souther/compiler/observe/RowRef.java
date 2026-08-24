package souther.compiler.observe;

import souther.compiler.source.SourceId;

import java.util.Objects;

/**
 * Which row, said well enough that two rows are never one.
 *
 * <p>{@link RowIdentity} is what a row names itself and is not a key on its own. A row written with
 * no name is a {@link RowIdentity.Unnamed} counted within one source, so a behavior exampled in a
 * module and in an attached file has a first row in each — and one behavior's rows are gathered from
 * every source that writes one. So which source is part of saying which row.
 *
 * <p><b>Why it has to be a value and not a spelling.</b> These travel inside a {@code WeakeningSet},
 * which is a set: two facts that are one fact collapse, and two that are not must not. Two rows of
 * one behavior that both did not come back are two things an author has to go and look at, and
 * carried under an identity that could not tell them apart they arrived as one. The same held one
 * level up, where a reason about a row named the behavior and nothing else: a module's list of
 * reasons is kept one per identity, so the second undecided row of a behavior was dropped where the
 * list was built (issue #996).
 *
 * @param behavior the behavior the row is written for, which is whose measurement it counts against
 * @param source   the source it is written in, without which the ordinal of an unnamed row is not
 *                 an identity
 * @param identity what the row names itself
 */
public record RowRef(String behavior, SourceId source, RowIdentity identity) {

    public RowRef {
        Objects.requireNonNull(behavior, "a row is written for a behavior and says which");
        Objects.requireNonNull(source, "a row is written in a source and says which");
        Objects.requireNonNull(identity, "a row names itself");
    }

    /** The one this outcome is of, taking the source from where the row is written. */
    public static RowRef of(RowOutcome row) {
        return new RowRef(row.target(), sourceOf(row), row.identity());
    }

    /** Where the row is written, which every row of a compile has: it was read from a source that
     *  compile was handed. A row with no such place is this compiler having built one from nothing,
     *  and is said here rather than left to arrive as a reason nobody can act on. */
    private static SourceId sourceOf(RowOutcome row) {
        if (row.at().quotedFrom()
                instanceof souther.compiler.diag.QuotedFrom.ASourceThisCompileHolds(SourceId file)) {
            return file;
        }
        throw new IllegalArgumentException("a row of `" + row.target()
                + "` is written in no source this compile holds: " + row.identity().shown());
    }

    /**
     * As a person is shown it, given what the caller calls the source this row is written in.
     *
     * <p><b>Two rows never read as one.</b> The identity above is three things and this was two, so
     * a behavior with a first row in its module and a first row in an attached file was two facts
     * that a reader saw once — which is the same loss the identity was widened to stop, at the last
     * step (issue #996).
     *
     * <p>Which parts it takes is what the identity needs to stay apart. A row written with a name
     * carries one no other row of its behavior has, so the name and the behavior are enough and the
     * file it is in is noise. A row written without one is numbered within its source, so the
     * source is what tells it from the row of the same number in the file beside it.
     *
     * @param source what the caller calls this row's source. Named by the caller for the reason
     *               every other source in a report is: the identity a compile files a source under
     *               is a position in a list for a build and a URI for an editor, and neither is
     *               what a person is shown
     */
    public String shown(String source) {
        return identity instanceof RowIdentity.Named
                ? behavior + " " + identity.shown()
                : behavior + " " + identity.shown() + " in " + source;
    }
}
