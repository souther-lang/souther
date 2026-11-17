package souther.compiler.reading;

import souther.compiler.diag.Citation;

import java.util.Objects;

/**
 * A meeting the walk met and could not join to what a run records: why, and where the code that
 * meets is written.
 *
 * <p>The count of these is the list's size, so a count and the meetings it counts cannot differ.
 *
 * @param why the reason it could not be joined
 * @param at  where the meeting is, as a report may say it
 */
public record UnjoinedMeeting(WhyNotJoined why, Citation at) {

    public UnjoinedMeeting {
        Objects.requireNonNull(why, "a meeting is not joined for a reason");
        Objects.requireNonNull(at, "a meeting is somewhere");
    }
}
