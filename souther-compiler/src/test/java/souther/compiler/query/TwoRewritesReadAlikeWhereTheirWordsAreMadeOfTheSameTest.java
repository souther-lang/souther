package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.SourceOutcome;
import souther.compiler.observe.RowIdentity;
import souther.compiler.partition.Replacement;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.WrittenOwner;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which rewrites of a body read alike is asked of what their words are made of, and not of the
 * numbers the arms are counted by, nor of the types the words name.
 *
 * <p>Two arms may be counted differently and mean the same, two may be told apart by the numbers
 * and not by anything a reader is shown, and two types of two modules may be named alike. Judged
 * by the numbers or the types, the first pair would be parted where nothing in their words parts
 * them, and the others left alike where the words cannot say which is which.
 */
class TwoRewritesReadAlikeWhereTheirWordsAreMadeOfTheSameTest {

    private static final WrittenOwner OWNER = new WrittenOwner.Body("lib.m", "pick");

    private static final SourceOutcome.Arm HELD =
            new SourceOutcome.Held(new SourceOutcome.HeldBy.Condition());
    private static final SourceOutcome.Arm FAILED =
            new SourceOutcome.Failed(new SourceOutcome.FailedBy.Condition());

    private static SourceConstructOrigin construct(int ordinal, SourceConstruct kind) {
        return SourceConstructOrigin.written(OWNER, ordinal, kind);
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

    private static SourceOutcome.Arm cased(String module, String name) {
        return new SourceOutcome.Matched(List.of(TypeSymbols.declared(new TypeKey(module, name))));
    }

    private static List<Optional<ReplacementEvidence.ToldApartBy>> toldApart(
            ReplacementEvidence.Summary summary) {
        return summary.rewrites().stream()
                .map(each -> summary.toldApartBy(each.replacement())).toList();
    }

    /** Arms whose words differ are not alike, whichever constructs they are of. */
    @Test
    void armsWhoseWordsDifferAreToldApartByNothing() {
        SourceConstructOrigin fork = construct(0, SourceConstruct.IF);
        ReplacementEvidence.Summary summary = new ReplacementEvidence.Summary(List.of(
                arm(fork, 0, 1, HELD, FAILED), arm(fork, 1, 0, FAILED, HELD)));

        assertEquals(List.of(Optional.empty(), Optional.empty()), toldApart(summary));
    }

    /** The same words of two constructs of one definition are told apart by the construct. */
    @Test
    void sameWordsOfTwoConstructsAreToldApartByTheConstruct() {
        ReplacementEvidence.Summary summary = new ReplacementEvidence.Summary(List.of(
                arm(construct(0, SourceConstruct.IF), 0, 1, HELD, FAILED),
                arm(construct(2, SourceConstruct.IF), 0, 1, HELD, FAILED)));

        assertEquals(List.of(
                        Optional.of(new ReplacementEvidence.ToldApartBy(0, 0, Optional.empty())),
                        Optional.of(new ReplacementEvidence.ToldApartBy(2, 0, Optional.empty()))),
                toldApart(summary));
    }

    /**
     * Two arms of one construct the words cannot part, counted differently. The construct says the
     * same of both, so the numbers they are counted by are what is left to say.
     */
    @Test
    void armsOfOneConstructThatMeanTheSameAreToldApartByTheirNumbers() {
        SourceConstructOrigin fork = construct(3, SourceConstruct.IF);
        ReplacementEvidence.Summary summary = new ReplacementEvidence.Summary(List.of(
                arm(fork, 0, 2, HELD, FAILED), arm(fork, 1, 2, HELD, FAILED)));

        assertEquals(List.of(
                        Optional.of(new ReplacementEvidence.ToldApartBy(3, 0,
                                Optional.of(new ReplacementEvidence.ToldApartBy.Arms(0, 2)))),
                        Optional.of(new ReplacementEvidence.ToldApartBy(3, 0,
                                Optional.of(new ReplacementEvidence.ToldApartBy.Arms(1, 2))))),
                toldApart(summary));
    }

    /**
     * An attempted construction under an {@code if} and under a {@code guard} are two constructs
     * and one pair of words, {@code constructed} and {@code else}. Alike to a reader, so each says
     * what tells it apart.
     */
    @Test
    void anAttemptUnderAnIfAndUnderAGuardAreAlikeToAReader() {
        SourceOutcome.Arm built = new SourceOutcome.Held(new SourceOutcome.HeldBy.Construction());
        SourceOutcome.Arm refused = new SourceOutcome.Failed(
                new SourceOutcome.FailedBy.Construction(Optional.empty()));
        ReplacementEvidence.Summary summary = new ReplacementEvidence.Summary(List.of(
                arm(construct(1, SourceConstruct.IF), 0, 1, built, refused),
                arm(construct(2, SourceConstruct.GUARD), 0, 1, built, refused)));

        assertEquals(List.of(
                        Optional.of(new ReplacementEvidence.ToldApartBy(1, 0, Optional.empty())),
                        Optional.of(new ReplacementEvidence.ToldApartBy(2, 0, Optional.empty()))),
                toldApart(summary));
    }

    /**
     * And where the two constructs call their ways through them differently, as they do for a
     * condition — {@code then} against {@code continued} — nothing more is said: the words part
     * them already.
     */
    @Test
    void aConditionUnderAnIfAndUnderAGuardAreNotAlike() {
        ReplacementEvidence.Summary summary = new ReplacementEvidence.Summary(List.of(
                arm(construct(1, SourceConstruct.IF), 0, 1, HELD, FAILED),
                arm(construct(2, SourceConstruct.GUARD), 0, 1, HELD, FAILED)));

        assertEquals(List.of(Optional.empty(), Optional.empty()), toldApart(summary));
    }

    /**
     * Two types of two modules named alike are two types to the compiler and one word to a
     * reader. Arms of one {@code match} that name them answer as each other in words that are the
     * same, so they are alike, and are told apart by the numbers they are counted by.
     */
    @Test
    void typesOfTwoModulesNamedAlikeAreAlikeToAReader() {
        SourceConstructOrigin match = construct(1, SourceConstruct.MATCH);
        SourceOutcome.Arm alpha = cased("alpha", "Foo");
        SourceOutcome.Arm beta = cased("beta", "Foo");
        assertNotEquals(alpha, beta, "two types to the compiler");

        ReplacementEvidence.Summary summary = new ReplacementEvidence.Summary(List.of(
                arm(match, 0, 1, alpha, beta), arm(match, 1, 0, beta, alpha)));

        List<Optional<ReplacementEvidence.ToldApartBy>> told = toldApart(summary);

        assertTrue(told.stream().allMatch(Optional::isPresent),
                () -> "alike to a reader, so each says what tells it apart: " + told);
        assertNotEquals(told.get(0), told.get(1), "and the two say different things");
    }
}
