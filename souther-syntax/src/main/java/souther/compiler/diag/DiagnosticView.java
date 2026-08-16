package souther.compiler.diag;

import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * One diagnostic as it reads from one of the sources it is said at: what its primary came to, the
 * place in that source it is anchored to, every other place it points at, and what it has to say
 * about code it cannot point at at all.
 *
 * <p>A problem written in two files is one diagnostic and is said in both. Which of its places is
 * the anchor therefore depends on which file is being read: on the row's file the anchor is what the
 * message is about and the stand-in is elsewhere, and on the stand-in's file the two change places.
 * The caret, the editor's squiggle and the linked locations all follow from that, so it is worked
 * out once here rather than in each reader.
 *
 * <p>{@code unquotable} is the third thing, and it is the same on every source: a clause written in
 * a module this compile has no file for is not in one file rather than another, so which file is
 * being read decides nothing about it.
 *
 * <p>A reader that quotes only one file — the command line and the annotation processor — asks for
 * the view on the source the report is listed under, where the anchor is what the message is about
 * and nothing changes places.
 *
 * @param primary what the report's own place came to, whether or not it is the anchor here. Carried
 *        so that a surface with no anchor is told which of the reasons it is: a report about no
 *        stretch of text, one whose code is out of sight, or one the caller did not say which text
 *        it was reading
 * @param anchor the place this file's marker goes on, and none where the report is listed on this
 *        file without pointing into it
 */
public record DiagnosticView(SpotResolution primary, Optional<Shown> anchor,
                             List<Shown> others, List<Unquotable> unquotable) {

    public DiagnosticView {
        Objects.requireNonNull(primary, "a view says what the report's own place came to");
        Objects.requireNonNull(anchor, "a view says whether this file has an anchor");
    }

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
     * How {@code d} reads from {@code published}, given what {@code context} says the surface is
     * listing it under and reading.
     *
     * <p>The anchor is the first place in the published source, taking what the message is about
     * before the labels and the labels in the order they were added. Declaration order settles it
     * because it is what the site that found the problem chose; the alternative, the earliest line,
     * would let the line numbers a file happens to have decide which of two notes is the one the
     * editor puts its marker on.
     *
     * <p>A source none of the places is in is refused, unless it is the source the report is listed
     * under. There is nothing to anchor there and no reason for a caller to be asking — where the
     * report is said is worked out from where it points. Being listed on a file is the one way a
     * report reaches a file it points into no part of, and that is a report about the file rather
     * than about a line of it.
     *
     * @throws IllegalArgumentException when no place of {@code d} is in {@code published} and the
     *         report is not listed under it either
     */
    public static DiagnosticView of(Diagnostic d, ReportContext context) {
        // Which file this view is for is the text the surface says it is reading, and is not a third
        // thing to be told. Handed over separately it was a source identity beside a diagnostic —
        // one more pair a caller could get out of step, and one nothing kept in step.
        SourceId published = context.textBeingRead()
                .flatMap(TextBeingRead::identity).orElse(null);
        SpotResolution primary = SpotResolution.of(d.primary(), context);
        List<Shown> shown = new ArrayList<>();
        if (primary instanceof SpotResolution.Found(Spot spot)) {
            shown.add(new Shown.ItsSubject(spot));
        }
        List<Unquotable> unquotable = new ArrayList<>();
        for (LabeledRegion label : d.secondary()) {
            switch (label.place()) {
                case DiagnosticPlace.InSource in ->
                        shown.add(new Shown.ALabel(new Spot.InSource(in), label.said()));
                case DiagnosticPlace.Unavailable out ->
                        unquotable.add(new Unquotable(out, label.said()));
            }
        }
        int at = anchorAmong(shown, published);
        if (at < 0 && !Objects.equals(context.filedUnder().orElse(null), published)) {
            throw new IllegalArgumentException(
                    "no place of this diagnostic is in " + published
                            + " and it is not listed under it either; it points into "
                            + shown.stream().map(Shown::spot).toList());
        }
        List<Shown> others = new ArrayList<>(shown.size());
        for (int i = 0; i < shown.size(); i++) {
            if (i != at) {
                others.add(shown.get(i));
            }
        }
        return new DiagnosticView(primary,
                at < 0 ? Optional.empty() : Optional.of(shown.get(at)),
                List.copyOf(others), List.copyOf(unquotable));
    }

    /**
     * Which of {@code shown} is in {@code published}, or -1.
     *
     * <p>Compared through {@link Spot#knownToBeOneText}, so a place is the anchor when it can be
     * shown to be in that file and not when nothing rules it out. A place in a text the surface
     * named answers here as readily as one in a source, which is what lets an editor anchor a report
     * parsed out of the very document it is publishing.
     */
    private static int anchorAmong(List<Shown> shown, SourceId published) {
        // A caller naming no file is not asking which of several it is reading: it has one text and
        // everything is quoted from it, so the first place is the one the marker goes on. Read as
        // "no place is in this file", it would leave a caller that holds the text with no caret.
        if (published == null) {
            return shown.isEmpty() ? -1 : 0;
        }
        for (int i = 0; i < shown.size(); i++) {
            if (Spot.knownToBeIn(shown.get(i).spot(), published)) {
                return i;
            }
        }
        return -1;
    }
}
