package souther.compiler.diag;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * One diagnostic as it reads from one of the sources it is said at: the place in that source it is
 * anchored to, every other place it points at, and what it has to say about code it cannot point at
 * at all.
 *
 * <p>A problem written in two files is one diagnostic and is said in both. Which of its regions is
 * the anchor therefore depends on which file is being read: on the row's file the anchor is the
 * primary region and the stand-in is elsewhere, and on the stand-in's file the two change places.
 * The caret, the editor's squiggle and the linked locations all follow from that, so it is worked
 * out once here rather than in each reader.
 *
 * <p>{@code unquotable} is the third thing, and it is the same on every source: a clause written in
 * a module this compile has no file for is not in one file rather than another, so which file is
 * being read decides nothing about it. It used to be dropped — by the clause reader, by the adequacy
 * warning, by moving a caret — each of which turned "the code is over there" into silence.
 *
 * <p>A reader that quotes only one file — the command line and the annotation processor — asks for
 * the view on the diagnostic's own source, where the anchor is always the primary region and
 * nothing changes places.
 */
public record DiagnosticView(Spot anchor, List<Spot> others, List<Unquotable> unquotable) {

    /**
     * Something a report has to say about code it cannot point at: where that code came from, and
     * what is being said about it.
     *
     * <p>Its own type rather than a {@link LabeledRegion} the readers cast. Held as labels, the rule
     * that every one of them is {@link DiagnosticPlace.Unavailable} lived in this class's factory
     * and in three casts written against it, which is a convention and not a fact — the same shape
     * this whole change is about, one level up.
     */
    public record Unquotable(DiagnosticPlace.Unavailable place,
                             souther.compiler.diag.msg.Message said) {

        public Unquotable {
            Objects.requireNonNull(place, "something said about code out of sight says where it is");
            Objects.requireNonNull(said, "something said about code out of sight says something");
        }
    }

    /**
     * How {@code d} reads from {@code publishedSourceId}, given that its primary region is in
     * {@code primarySourceId}.
     *
     * <p>The anchor is the first place in the published source, taking the primary region before the
     * secondaries and the secondaries in the order they were added. Declaration order settles it
     * because it is what the site that found the problem chose; the alternative, the earliest line,
     * would let the line numbers a file happens to have decide which of two notes is the one the
     * editor puts its marker on.
     *
     * <p>A source none of the regions is in is refused. There is nothing to anchor there, and the
     * nearest thing to an answer — the primary region — is a line and a column from another file,
     * which in that one points at whatever happens to sit at those numbers. Where a diagnostic is
     * said is worked out from where it points, so a source that has nothing here is a caller asking
     * about a file this was never going to be said in.
     *
     * @throws IllegalArgumentException when no region of {@code d} is in {@code publishedSourceId}
     */
    public static DiagnosticView of(Diagnostic d, String primarySourceId, String publishedSourceId) {
        List<Spot> spots = new ArrayList<>();
        List<Unquotable> unquotable = new ArrayList<>();
        spots.add(Spot.primary(d, primarySourceId));
        for (LabeledRegion label : d.secondary()) {
            switch (label.place()) {
                case DiagnosticPlace.InSource in ->
                        spots.add(Spot.secondary(in, label.said()));
                case DiagnosticPlace.Unavailable out ->
                        unquotable.add(new Unquotable(out, label.said()));
            }
        }
        int at = -1;
        for (int i = 0; i < spots.size(); i++) {
            if (Objects.equals(spots.get(i).sourceId(), publishedSourceId)) {
                at = i;
                break;
            }
        }
        if (at < 0) {
            throw new IllegalArgumentException(
                    "no region of this diagnostic is in " + publishedSourceId
                            + "; it points into " + spots.stream().map(Spot::sourceId).toList());
        }
        List<Spot> others = new ArrayList<>(spots.size() - 1);
        for (int i = 0; i < spots.size(); i++) {
            if (i != at) {
                others.add(spots.get(i));
            }
        }
        return new DiagnosticView(spots.get(at), List.copyOf(others), List.copyOf(unquotable));
    }
}
