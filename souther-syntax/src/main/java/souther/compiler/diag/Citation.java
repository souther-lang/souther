package souther.compiler.diag;

import souther.compiler.source.SourceId;

import java.util.LinkedHashMap;
import java.util.SequencedMap;

/**
 * Where the code something is about is written, as a report is entitled to say it.
 *
 * <p>A coordinate is put to two uses and only one of them can be wrong. Sending a reader somewhere —
 * a caret, a range, an editor jumping — is right whatever the coordinate stands for, because it is
 * where this compile met the code and the only place a reader can be sent. Saying the code is
 * <em>written</em> there is right only where it is. Nothing distinguished the two, so every surface
 * that wanted the first published the second: an unreached arm of {@code List.filter} was reported
 * at the caller's {@code 15:23} by the adequacy report in both of its renderings and by the JSON a
 * diagnostic is read from, and one renderer out of four said what the coordinate stood for.
 *
 * <p>So the two are separate values. {@link SourcePos} is where this compile placed a node, and every
 * pass reads it freely. This is the other one, and it is what a report holds: a coverage site, a
 * finding, a reason carries this rather than a coordinate, so a surface written later is handed the
 * answer rather than the raw place.
 *
 * <p>No accessor spans the two cases. A reader that wants the coordinate — to put a caret at it —
 * says which case it is in first, and having said so has seen that the other exists. An
 * {@code at()} on this interface would be the shortest way back to the defect: every caller would
 * write it, the sum would decorate nothing, and the second case would go unread again.
 *
 * <p>Built one way. {@link #of} asks the coordinate's provenance to project itself, which is the only
 * thing {@link WrittenAt} will do and is package-private so that it stays so, and the arms cannot be
 * built or implemented from outside this package. So there is no independent construction path: every
 * citation is a projection of provenance a coordinate already carries.
 *
 * <p>Which is a rule about where a statement comes from and not a claim that provenance is a secret.
 * A caller may stamp a coordinate itself and project that, and may compare a provenance against one
 * it builds. What it may not do is read the declaration off a coordinate and write a place of its
 * own, which is the defect this exists to close.
 */
public sealed interface Citation permits Citation.Written, Citation.OutOfSight {

    /** The code is written at {@link #at()}, which is therefore both where to send a reader and
     *  where the code is. */
    sealed interface Written extends Citation permits WrittenCitation {
        SourcePos at();
    }

    /**
     * The code is written where {@link #provenance()} says, which this compile has no source for.
     * {@link #reachedFrom()} is where this compile met it — where to send a reader, and not where the
     * code is.
     */
    sealed interface OutOfSight extends Citation permits OutOfSightCitation {
        /** Where that code came from, and the name a reader here reaches it by:
         *  {@code List.filter}. */
        SourceProvenance provenance();

        /** The call the body was spliced into. A place in a file the reader holds. */
        SourcePos reachedFrom();
    }

    /**
     * What a report may say about where {@code pos} names code written.
     *
     * <p>Of the coordinate, and a citation holds that coordinate with nothing beside it. The
     * coordinate has said which source it is in since positions were gathered across files, so an
     * identity held next to one is a second answer to a question already answered, the two can
     * disagree, and a citation holding both is a place that is two places — which is how a report
     * came to write one source's identity beside another source's line and column.
     */
    static Citation of(SourcePos pos) {
        return pos.writtenAt().cite(pos);
    }

    /**
     * What a document writes about this, as the fields it writes them under.
     *
     * <p>One writer for two documents. The adequacy report and the JSON a diagnostic is read from
     * both say this, and a consumer reading one of them should not have to learn a second vocabulary
     * to read the other — which is what would have happened, the two being rendered in different
     * modules by different machinery.
     *
     * <p>Written on both arms, {@code here} included. The field is added to a schema that already has
     * documents without it, so its absence has to go on meaning "this document does not say" — and an
     * emitter that wrote it only where the answer was interesting would put "the code is here" and
     * "written before anyone asked" under one silence.
     */
    default SequencedMap<String, String> writtenAtFields() {
        SequencedMap<String, String> fields = new LinkedHashMap<>();
        switch (this) {
            case Written _ -> fields.put("kind", "here");
            case OutOfSight out -> fields.putAll(outOfSightFields(out.provenance()));
        }
        return fields;
    }

    /**
     * The same fields for code out of sight, said of a provenance rather than of a citation.
     *
     * <p>For a report with nowhere to point: a label about a clause of a module this compile holds
     * no file for has the provenance and no coordinate to project. One writer, so the words a
     * document uses for "the code is elsewhere" are the same whether or not there was a caret.
     */
    static SequencedMap<String, String> outOfSightFields(SourceProvenance provenance) {
        SequencedMap<String, String> fields = new LinkedHashMap<>();
        fields.put("kind", "outOfSight");
        fields.put("declaration", provenance.reachedBy());
        return fields;
    }

    /**
     * This as a line of a report about {@code sectionSource}, with the sources under the names
     * {@code names} gives them.
     *
     * <p>A line and a column are a place only beside a file. They are written on their own where the
     * section already names the file, and with the file where it does not — a coordinate from another
     * source, printed bare, points at whatever happens to sit at those numbers in the one the reader
     * has in mind.
     */
    default String said(SourceNameResolver names, SourceId sectionSource) {
        return switch (this) {
            case Written written -> place(written.at(), names, sectionSource);
            case OutOfSight out -> "`" + out.provenance().reachedBy() + "`, reached at "
                    + place(out.reachedFrom(), names, sectionSource);
        };
    }

    /** Never handed a null: both arms require the place they are about. The tolerance the report's
     *  own writer used to have is gone rather than carried over, and a fallback standing in for it
     *  would read as a case somebody had thought about. */
    private static String place(SourcePos at, SourceNameResolver names, SourceId sectionSource) {
        if (at.sourceId() == null || at.sourceId().equals(sectionSource)) {
            return String.valueOf(at);
        }
        return names.nameOf(at.sourceId()) + ":" + at;
    }
}
