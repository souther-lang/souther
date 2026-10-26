package souther.compiler.partition;

import java.util.Objects;

/**
 * What a row is written against: what its parameters are and how a value of each is written, and
 * what the decoder says of a value put at one.
 *
 * <p>Both, because writing a row again from the values its run observed needs the first to spell
 * the values and the second to refuse the ones the rules do not admit before anything runs.
 *
 * @param subject what the parameters are and how a value of each is written
 * @param check   whether the decoder builds a value written at a parameter
 */
public record RowWriting(MeasuredInput subject, Generator.CandidateCheck check) {

    public RowWriting {
        Objects.requireNonNull(subject, "rows are written for some parameters");
        Objects.requireNonNull(check, "a value written is held to the decoder");
    }
}
