package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.SourceOutcome;
import souther.compiler.observe.RowIdentity;
import souther.compiler.partition.Replacement;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.HashSet;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * Which rewrites of a body read alike is asked of what their words are made of, and not of the
 * numbers the arms are counted by.
 *
 * <p>Two arms may be counted differently and mean the same, and two may be told apart by the
 * numbers and not by anything a reader is shown. Judged by the numbers, the first pair would be
 * parted where nothing in their words parts them, and the second left alike where the words
 * cannot say which is which.
 */
class TwoRewritesReadAlikeWhereTheirWordsAreMadeOfTheSameTest {

    private static final WrittenOwner OWNER = new WrittenOwner.Body("lib.m", "pick");

    private static final SourceOutcome.Arm HELD =
            new SourceOutcome.Held(new SourceOutcome.HeldBy.Condition());
    private static final SourceOutcome.Arm FAILED =
            new SourceOutcome.Failed(new SourceOutcome.FailedBy.Condition());

    private static SourceConstructOrigin fork(int ordinal) {
        return SourceConstructOrigin.written(OWNER, ordinal, SourceConstruct.IF);
    }

    private static ReplacementEvidence.Rewrite arm(SourceConstructOrigin fork, int part, int with,
                                                   SourceOutcome.Arm arm,
                                                   SourceOutcome.Arm sibling) {
        Replacement.OfAnArm replacement = new Replacement.OfAnArm(fork, part, with);
        return new ReplacementEvidence.Rewrite(
                new ReplacementAsWritten.OfAnArm(replacement, arm, sibling),
                new ReplacementReportAnchor.AtTheBehavior(),
                new ReplacementEvidence.Noticed(new RowIdentity.Unnamed(1)));
    }

    private static List<String> said(ReplacementEvidence.Summary summary) {
        return summary.rewrites().stream()
                .map(each -> summary.constructSaidBeside(each.replacement())).toList();
    }

    /** Arms whose words differ are not alike, whichever constructs they are of. */
    @Test
    void armsWhoseWordsDifferAreSaidWithNothingBeside() {
        ReplacementEvidence.Summary summary = new ReplacementEvidence.Summary(List.of(
                arm(fork(0), 0, 1, HELD, FAILED), arm(fork(0), 1, 0, FAILED, HELD)));

        assertEquals(List.of("", ""), said(summary));
    }

    /** The same words of two constructs of one definition are told apart by the construct. */
    @Test
    void sameWordsOfTwoConstructsAreToldApartByTheConstruct() {
        ReplacementEvidence.Summary summary = new ReplacementEvidence.Summary(List.of(
                arm(fork(0), 0, 1, HELD, FAILED), arm(fork(2), 0, 1, HELD, FAILED)));

        assertEquals(List.of(" (construct 0)", " (construct 2)"), said(summary));
    }

    /**
     * Two arms of one construct the words cannot part, counted differently. The construct says the
     * same of both, so the numbers they are counted by are what is left to say.
     */
    @Test
    void armsOfOneConstructThatMeanTheSameAreToldApartByTheirNumbers() {
        ReplacementEvidence.Summary summary = new ReplacementEvidence.Summary(List.of(
                arm(fork(3), 0, 2, HELD, FAILED), arm(fork(3), 1, 2, HELD, FAILED)));

        List<String> said = said(summary);

        assertEquals(2, new HashSet<>(said).size(), () -> "no two the same: " + said);
        assertNotEquals("", said.getFirst());
    }
}
