package souther.compiler.diag;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * One diagnostic as it reads from one of the sources it is said at: the place in that source it is
 * anchored to, and every other place it points at.
 *
 * <p>A problem written in two files is one diagnostic and is said in both. Which of its regions is
 * the anchor therefore depends on which file is being read: on the row's file the anchor is the
 * primary region and the stand-in is elsewhere, and on the stand-in's file the two change places.
 * The caret, the editor's squiggle and the linked locations all follow from that, so it is worked
 * out once here rather than in each reader.
 *
 * <p>A reader that quotes only one file — the command line and the annotation processor — asks for
 * the view on the diagnostic's own source, where the anchor is always the primary region and
 * nothing changes places.
 */
public record DiagnosticView(Spot anchor, List<Spot> others) {

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
     * <p>A published source none of the regions is in leaves the primary region as the anchor, so a
     * caller that asks about the wrong source quotes the diagnostic's own file rather than nothing.
     */
    public static DiagnosticView of(Diagnostic d, String primarySourceId, String publishedSourceId) {
        List<Spot> spots = new ArrayList<>();
        spots.add(Spot.primary(d, primarySourceId));
        for (LabeledRegion label : d.secondary()) {
            spots.add(Spot.secondary(label, primarySourceId));
        }
        int at = 0;
        for (int i = 0; i < spots.size(); i++) {
            if (Objects.equals(spots.get(i).sourceId(), publishedSourceId)) {
                at = i;
                break;
            }
        }
        List<Spot> others = new ArrayList<>(spots.size() - 1);
        for (int i = 0; i < spots.size(); i++) {
            if (i != at) {
                others.add(spots.get(i));
            }
        }
        return new DiagnosticView(spots.get(at), List.copyOf(others));
    }
}
