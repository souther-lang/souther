package souther.runtime;

import java.util.function.Predicate;
import net.unit8.notation199x.CaseConversion;
import net.unit8.notation199x.Checkpoint;
import net.unit8.notation199x.Normalization;
import net.unit8.notation199x.Normalization.Form;
import net.unit8.notation199x.Outcome;
import net.unit8.notation199x.ScalarValues;
import net.unit8.notation199x.pattern.StringPattern;
import org.jspecify.annotations.Nullable;

/**
 * The text rules of 199x-notation this runtime runs, each under a {@link WorkCheckpoint}.
 *
 * <p>Where the checkpoint is {@link WorkCheckpoint#NONE} the rule is run by its entry that takes
 * none, which is what a shipped class reaches. Otherwise it is run by the entry that asks a
 * checkpoint as it goes, and the work checkpoint is what it asks.
 *
 * <p>The library's checkpoint answers whether to go on, and a rule answers {@link Outcome.Stopped}
 * where it is told not to. A work checkpoint never says not to go on: it passes, or it throws, and
 * the library lets what a checkpoint throws out as it is. So a rule run from here always answers.
 */
final class TextRules {

    private TextRules() {}

    static int halfAPairAt(String text, WorkCheckpoint checkpoint) {
        return checkpoint == WorkCheckpoint.NONE ? ScalarValues.halfAPairAt(text)
                : answer(ScalarValues.halfAPairAt(text, asked(checkpoint)));
    }

    static long count(String text, WorkCheckpoint checkpoint) {
        return checkpoint == WorkCheckpoint.NONE ? ScalarValues.count(text)
                : answer(ScalarValues.count(text, asked(checkpoint)));
    }

    static int compare(String a, String b, WorkCheckpoint checkpoint) {
        return checkpoint == WorkCheckpoint.NONE ? ScalarValues.compare(a, b)
                : answer(ScalarValues.compare(a, b, asked(checkpoint)));
    }

    static @Nullable String nfcWithin(String text, long longest, WorkCheckpoint checkpoint) {
        return checkpoint == WorkCheckpoint.NONE ? Normalization.normalizeWithin(Form.NFC, text, longest)
                : answer(Normalization.normalizeWithin(Form.NFC, text, longest, asked(checkpoint)));
    }

    static @Nullable String lowercaseWithin(String text, long longest, WorkCheckpoint checkpoint) {
        return checkpoint == WorkCheckpoint.NONE ? CaseConversion.lowercaseWithin(text, longest)
                : answer(CaseConversion.lowercaseWithin(text, longest, asked(checkpoint)));
    }

    static @Nullable String uppercaseWithin(String text, long longest, WorkCheckpoint checkpoint) {
        return checkpoint == WorkCheckpoint.NONE ? CaseConversion.uppercaseWithin(text, longest)
                : answer(CaseConversion.uppercaseWithin(text, longest, asked(checkpoint)));
    }

    /** Whether the machine {@link Patterns#read} made accepts {@code subject}. */
    static boolean matches(Predicate<String> pattern, String subject, WorkCheckpoint checkpoint) {
        return checkpoint == WorkCheckpoint.NONE ? pattern.test(subject)
                : answer(((StringPattern) pattern).matches(subject, asked(checkpoint)));
    }

    /** {@code checkpoint} as the library asks one. */
    private static Checkpoint asked(WorkCheckpoint checkpoint) {
        return () -> {
            checkpoint.pass();
            return true;
        };
    }

    private static <T extends @Nullable Object> T answer(Outcome<T> outcome) {
        return switch (outcome) {
            case Outcome.Answered<T>(var answer) -> answer;
            case Outcome.Stopped<T> _ -> throw new IllegalStateException(
                    "a text rule stopped, and a work checkpoint never tells one to");
        };
    }
}
