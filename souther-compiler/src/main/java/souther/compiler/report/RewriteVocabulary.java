package souther.compiler.report;

import souther.compiler.diag.msg.Message;
import souther.compiler.diag.msg.ReportMessage;
import souther.compiler.observe.RowRef;
import souther.compiler.query.ReplacementAsWritten;
import souther.compiler.query.ReplacementEvidence;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * What a report calls a rewrite of a body.
 *
 * <p>Words that tell one rewrite from every other of the same body, or they say nothing a reader can
 * act on: an arm by the arm and the arm it answers as, in the words {@link ArmVocabulary} has for
 * an arm, and the body answering one value by the row that came to that value, which is how a
 * reader outside this compiler is sent to it. Here, once, for every reader that writes one — a
 * line under a measure and a row composed for it are two places one rewrite is met, and two
 * spellings of it would read as two rewrites.
 *
 * <p>The messages and not their words, which are the catalog's in the reader's language. An arm's
 * label is the language's own spelling of the arm and is the same in every one.
 *
 * <p>No place. Where a rewrite of an arm is shown is the finding's to say, and a reader puts it
 * beside these words where its sentence wants it; a fork this build holds no source of has none,
 * and is said by the definition that wrote it instead ({@link #outOfSight}).
 */
final class RewriteVocabulary {

    /**
     * Where the fork of a rewrite this build holds no source of is, as far as this build can say:
     * the definition that wrote it ({@link ReplacementAsWritten.OfAnArm#writtenBy}), as a reader of
     * {@code module} names a definition of another module.
     */
    static Message outOfSight(ReplacementAsWritten.OfAnArm rewrite, String module) {
        return new ReportMessage.InAForkOutOfSight(rewrite.writtenBy().saidIn(module));
    }

    /**
     * Where the fold of a rewrite this build holds no source of is, as far as this build can say:
     * the definition that wrote it, as {@link #outOfSight(ReplacementAsWritten.OfAnArm, String)}
     * says a fork's.
     */
    static Message outOfSight(ReplacementAsWritten.OfAWalk rewrite, String module) {
        return new ReportMessage.InADefinitionOutOfSight(rewrite.writtenBy().saidIn(module));
    }

    /**
     * What tells a rewrite from one whose words read the same, as the end of a phrase about it;
     * nothing where its words already differ.
     *
     * <p>The numbers the document writes as {@code construct} and {@code lowered}, and no place: a
     * definition this build holds no source of has no line to give, and one made up would send a
     * reader to code that is not there. They tell the lines apart and are not where to look.
     */
    static Message apart(Optional<ReplacementEvidence.ToldApartBy> by) {
        return by.<Message>map(it -> {
            List<Message> parts = new ArrayList<>();
            parts.add(new ReportMessage.AtTheConstruct(Integer.toString(it.construct())));
            if (it.lowered() != 0) {
                parts.add(new ReportMessage.Lowered(Integer.toString(it.lowered())));
            }
            it.arms().ifPresent(arms -> parts.add(new ReportMessage.ArmAs(
                    String.valueOf(arms.part()), String.valueOf(arms.with()))));
            Message said = parts.getLast();
            for (int i = parts.size() - 2; i >= 0; i--) {
                said = new ReportMessage.PartsOfOne(parts.get(i), said);
            }
            return new ReportMessage.Bracketed(said);
        }).orElse(new ReportMessage.Nothing());
    }

    /** What {@code rewrite} has the fold do, as the end of a sentence about the fold. */
    static Message walked(ReplacementAsWritten.OfAWalk rewrite) {
        return switch (rewrite.replacement().how()) {
            case STOPS_AFTER_ONE_STEP -> new ReportMessage.StoppedAfterItsFirstElement();
            case STEPS_FROM_THE_SEED -> new ReportMessage.HandedEachStepTheSeed();
        };
    }

    /** The word for the arm {@code rewrite} rewrites. */
    static String rewritten(ReplacementAsWritten.OfAnArm rewrite) {
        return ArmVocabulary.label(rewrite.replacement().fork().kind(), rewrite.arm());
    }

    /** The word for the arm {@code rewrite} has it answer as. */
    static String answeredAs(ReplacementAsWritten.OfAnArm rewrite) {
        return ArmVocabulary.label(rewrite.replacement().fork().kind(), rewrite.sibling());
    }

    /**
     * The row that came to the value {@code rewrite} has the body answer, in the words a report
     * names a row in.
     */
    static Message answeredBy(ReplacementAsWritten.ByOneAnswer rewrite, Page page) {
        RowRef row = rewrite.replacement().answeredBy();
        return AdequacyReport.rowNamed(row, page);
    }

    /**
     * Short words for {@code rewrite}, which a row composed for it may be named by: the arm and
     * the arm it answers as, or the row whose value the body answers.
     */
    static Message label(ReplacementAsWritten rewrite, Page page) {
        return switch (rewrite) {
            case ReplacementAsWritten.OfAnArm arm ->
                    new ReportMessage.AnArmAnsweringAs(rewritten(arm), answeredAs(arm));
            case ReplacementAsWritten.ByOneAnswer one ->
                    new ReportMessage.TheBodyAnsweringWhatARowAnswers(answeredBy(one, page));
            case ReplacementAsWritten.OfAWalk walk -> switch (walk.replacement().how()) {
                case STOPS_AFTER_ONE_STEP -> new ReportMessage.TheFoldStoppingAfterItsFirstElement();
                case STEPS_FROM_THE_SEED -> new ReportMessage.EachStepOfTheFoldHandedTheSeed();
            };
        };
    }

    private RewriteVocabulary() {}
}
