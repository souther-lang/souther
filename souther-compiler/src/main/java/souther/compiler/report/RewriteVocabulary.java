package souther.compiler.report;

import souther.compiler.diag.SourceRendering;
import souther.compiler.observe.RowRef;
import souther.compiler.query.ReplacementAsWritten;

/**
 * What the reports written in one language call a rewrite of a body.
 *
 * <p>Words that tell one rewrite from every other of the same body, or they say nothing a reader can
 * act on: an arm by the arm and the arm it answers as, in the words {@link ArmVocabulary} has for
 * an arm, and the body answering one value by the row that came to that value, which is how a
 * reader outside this compiler is sent to it. Here, once, for every reader that writes one — a
 * line under a measure and a row composed for it are two places one rewrite is met, and two
 * spellings of it would read as two rewrites.
 *
 * <p>No place. Where a rewrite of an arm is shown is the finding's to say, and a reader puts it
 * beside these words where its sentence wants it; a fork this build holds no source of has none,
 * and is said by the definition that wrote it instead ({@link #outOfSight}).
 */
public final class RewriteVocabulary {

    /**
     * Where the fork of a rewrite this build holds no source of is, as far as this build can say:
     * the definition that wrote it ({@link ReplacementAsWritten.OfAnArm#writtenBy}), as a reader of
     * {@code module} names a definition of another module.
     */
    public static String outOfSight(ReplacementAsWritten.OfAnArm rewrite, String module) {
        return "in a fork of `" + rewrite.writtenBy().saidIn(module)
                + "` this build holds no source of";
    }

    /**
     * Where the fold of a rewrite this build holds no source of is, as far as this build can say:
     * the definition that wrote it, as {@link #outOfSight(ReplacementAsWritten.OfAnArm, String)}
     * says a fork's.
     */
    public static String outOfSight(ReplacementAsWritten.OfAWalk rewrite, String module) {
        return "in `" + rewrite.writtenBy().saidIn(module) + "` this build holds no source of";
    }

    /** What {@code rewrite} has the fold do, as the end of a sentence about the fold. */
    public static String walked(ReplacementAsWritten.OfAWalk rewrite) {
        return switch (rewrite.replacement().how()) {
            case STOPS_AFTER_ONE_STEP -> "stopped after its first element";
            case STEPS_FROM_THE_SEED ->
                    "handed each step the seed in place of what the step before it answered";
        };
    }

    /** The word for the arm {@code rewrite} rewrites. */
    public static String rewritten(ReplacementAsWritten.OfAnArm rewrite) {
        return ArmVocabulary.label(rewrite.replacement().fork().kind(), rewrite.arm());
    }

    /** The word for the arm {@code rewrite} has it answer as. */
    public static String answeredAs(ReplacementAsWritten.OfAnArm rewrite) {
        return ArmVocabulary.label(rewrite.replacement().fork().kind(), rewrite.sibling());
    }

    /**
     * The row that came to the value {@code rewrite} has the body answer, in the words a report
     * names a row in.
     */
    public static String answeredBy(ReplacementAsWritten.ByOneAnswer rewrite,
                                    SourceRendering rendering) {
        RowRef row = rewrite.replacement().answeredBy();
        return row.shown(rendering.names().nameOf(row.source()));
    }

    /**
     * Short words for {@code rewrite}, which a row composed for it may be named by: the arm and
     * the arm it answers as, or the row whose value the body answers.
     */
    public static String label(ReplacementAsWritten rewrite, SourceRendering rendering) {
        return switch (rewrite) {
            case ReplacementAsWritten.OfAnArm arm ->
                    rewritten(arm) + " answering as " + answeredAs(arm);
            case ReplacementAsWritten.ByOneAnswer one ->
                    "the body answering what " + answeredBy(one, rendering) + " answers";
            case ReplacementAsWritten.OfAWalk walk -> switch (walk.replacement().how()) {
                case STOPS_AFTER_ONE_STEP -> "the fold stopping after its first element";
                case STEPS_FROM_THE_SEED -> "each step of the fold handed the seed";
            };
        };
    }

    private RewriteVocabulary() {}
}
