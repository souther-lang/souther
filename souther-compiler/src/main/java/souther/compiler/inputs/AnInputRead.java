package souther.compiler.inputs;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.revision.RevisionKnowledge;
import souther.compiler.revision.RevisionWork;

import java.util.Objects;

/**
 * One behavior's input read, as work settled by the input and the source its rules are read from.
 *
 * <p>What makes a measurement of a behavior one measurement. Its division, the subject a row is
 * written for, the meetings its body holds and the decisions it makes are each a question of their
 * own, and each needs the input read: asked of {@link InputDomain#reading} at each of them, every
 * rule of every parameter is read again to come to the answers the first reading came to, and
 * what the reading keeps of the contexts it was asked under starts again from nothing. Settled
 * here, the first of them reads the input and the rest are lent that reading.
 *
 * <p>Beside {@link InputDomain} and not inside it. Reading an input is what that value does when it
 * is asked; whether somebody in this revision has already asked is the revision's to know, and an
 * input that kept its readings would be a value holding the lifetime of whoever read it.
 *
 * <p>The source by its origin and not by the source handed over to do the work. A source is a
 * capability and compares as one, so two sources of one module's rules are two objects; the origin
 * is what says they are one source ({@link RuleReadingSource.Origin}), and under one origin a
 * revision has one world to read in. The source is carried to do the work with and is no part of
 * which work this is.
 */
public final class AnInputRead implements RevisionWork<InputReading> {

    private final InputDomain input;

    private final RuleReadingSource.Origin origin;

    private final RuleReadingSource source;

    public AnInputRead(InputDomain input, RuleReadingSource source) {
        this.input = Objects.requireNonNull(input, "an input is what is read");
        this.origin = source.origin();
        this.source = source;
    }

    @Override
    public InputReading workedOut(RevisionKnowledge revision) {
        return input.reading(source);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof AnInputRead it && input.equals(it.input)
                && origin.equals(it.origin);
    }

    @Override
    public int hashCode() {
        return Objects.hash(input, origin);
    }

    @Override
    public String toString() {
        return "AnInputRead[" + input.parameters() + "]";
    }
}
