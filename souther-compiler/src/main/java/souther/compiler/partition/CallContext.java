package souther.compiler.partition;

import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ExpansionSite;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * Where the code a reading is walking stands: the body it was handed, or the body of a helper
 * that calls itself, read at one call of it.
 *
 * <p>A helper that calls itself is not copied into the body that calls it — it is one method,
 * whichever call runs it — so what it compares is one construct in one tree however many calls
 * there are. Read at a call, each of those comparisons is the rule of that call: two calls on two
 * containers are two rules about two positions, and what is filed about one must not land on the
 * other. So a construct met in the helper's body is the copy of it this call would make if it were
 * spliced in, which is what a construct of a non-recursive helper read at its call already is
 * ({@link ExpansionSite.Written}).
 *
 * <p>Only what a construct is in the model is moved. Where a run through it is recorded is the
 * helper's own place, which every call shares, and asked by the construct as the tree that runs
 * holds it.
 *
 * @param around      the copy a construct of the body read here stands in, or null in the body
 *                    the reading was handed
 * @param aroundModel the same, as the copies the model makes
 * @param helper      the helper whose body this is, or null in the body the reading was handed
 */
record CallContext(OccurrenceLineage around, ExpansionLineage aroundModel,
                   ValueName.Helper helper) {

    /** The body the reading was handed, where a construct is what it carries. */
    static final CallContext OF_THE_BODY = new CallContext(null, null, null);

    /** The occurrence {@code written}, as it stands where this reading is. */
    ConstructOccurrence of(ConstructOccurrence written) {
        if (around == null) {
            return written;
        }
        OccurrenceLineage moved = around;
        for (OccurrenceLineage step : stepsOf(written.lineage())) {
            moved = switch (step) {
                case OccurrenceLineage.Expansion copy -> moved.copiedInto(copy.expanded(), copy.at());
                case OccurrenceLineage.Materialisation build ->
                        moved.builtFor(build.materialised(), build.at());
                case OccurrenceLineage.Original _ -> moved;
            };
        }
        return new ConstructOccurrence(written.origin(), moved);
    }

    /** The construct of the model {@code written} is, as it stands where this reading is. */
    ModelOccurrence of(ModelOccurrence written) {
        if (aroundModel == null) {
            return written;
        }
        List<ExpansionLineage.Expansion> steps = new ArrayList<>();
        for (ExpansionLineage each = written.lineage();
                each instanceof ExpansionLineage.Expansion step; each = step.within()) {
            steps.add(0, step);
        }
        ExpansionLineage moved = aroundModel;
        for (ExpansionLineage.Expansion step : steps) {
            moved = moved.copiedInto(step.expanded(), step.at());
        }
        return new ModelOccurrence(written.origin(), moved);
    }

    /**
     * Where the body of {@code helper} is read at the call {@code call} of it standing here — or
     * null where the call is no call the source wrote, so no copy of the helper can be said to be
     * made at it, or where the reading is inside a call of {@code helper} already.
     */
    CallContext into(ValueName.Helper helper, ConstructOccurrence call) {
        if (call == null || !call.origin().isWritten()
                || call.origin().kind() != SourceConstruct.CALL || inside(helper)) {
            return null;
        }
        ConstructOccurrence here = of(call);
        ModelOccurrence stated = ModelOccurrence.statedAt(here).orElse(null);
        if (stated == null) {
            return null;
        }
        ExpansionSite.Written site = new ExpansionSite.Written(call.origin());
        return new CallContext(here.lineage().copiedInto(helper, site),
                stated.lineage().copiedInto(helper, site), helper);
    }

    /** Whether the reading is inside a call of {@code helper}. */
    private boolean inside(ValueName.Helper helper) {
        for (OccurrenceLineage each = around; each != null; ) {
            switch (each) {
                case OccurrenceLineage.Expansion copy -> {
                    if (copy.expanded().equals(helper)) {
                        return true;
                    }
                    each = copy.within();
                }
                case OccurrenceLineage.Materialisation build -> each = build.within();
                case OccurrenceLineage.Original _ -> each = null;
            }
        }
        return false;
    }

    /** The steps of {@code lineage}, outermost first. */
    private static List<OccurrenceLineage> stepsOf(OccurrenceLineage lineage) {
        List<OccurrenceLineage> out = new ArrayList<>();
        for (OccurrenceLineage each = lineage; each != null; ) {
            switch (each) {
                case OccurrenceLineage.Expansion copy -> {
                    out.add(0, copy);
                    each = copy.within();
                }
                case OccurrenceLineage.Materialisation build -> {
                    out.add(0, build);
                    each = build.within();
                }
                case OccurrenceLineage.Original _ -> each = null;
            }
        }
        return out;
    }
}
