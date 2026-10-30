package souther.compiler.report;

import souther.compiler.partition.UndividedPosition;

/**
 * What a report says of a place it leaves undivided for {@code reason}, for a test that reads a
 * report as a reader does.
 *
 * <p>Asked of the report by the reason, so a test holds which reason a place was left with and not
 * a copy of how it is worded. Copied into each test, a sentence reworded in one place left the
 * others asserting words no report says, and a sentence another reason's words contain passed for
 * this one.
 */
public final class WhyAPlaceIsUndividedIsSaid {

    /** The words the report puts after the place's name for {@code reason}. */
    public static String of(UndividedPosition.Reason reason) {
        return AdequacyReport.whyUnread(reason);
    }

    private WhyAPlaceIsUndividedIsSaid() {}
}
