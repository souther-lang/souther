package souther.compiler.partition;

import souther.compiler.inputs.InputReading;
import souther.compiler.meaning.Proposition;

import java.util.List;

/**
 * What a statement about a dependency's answer asks of a value composed for it.
 *
 * <p>The reading the answer's type was read by, kept beside the subject a value is composed over
 * and not inside it. A statement made over the subject is turned into the demands a row is
 * composed against by the reading a condition of a body is, and what leaves is the demand: nothing
 * that searches for a value reaches the reading, which is what the subject is held apart from it
 * for.
 *
 * <p>Held where the composition is asked and not in any answer: two of these are two readings, and
 * the subject beside it is what says whether two compositions are the same.
 */
public final class AnswerStatements {

    /** For a composition that was handed no reading: a statement it is asked to meet is one it
     *  says it did not compose against. */
    public static final AnswerStatements NONE = new AnswerStatements(null);

    private final InputReading reading;

    private AnswerStatements(InputReading reading) {
        this.reading = reading;
    }

    /** The statements of the answer {@code reading} is the reading of. */
    public static AnswerStatements of(InputReading reading) {
        if (reading == null) {
            throw new IllegalArgumentException("statements are asked of the reading of an answer");
        }
        return new AnswerStatements(reading);
    }

    /**
     * What {@code stated} asks of a row, or null where there is no reading to ask it of.
     *
     * @param stated a statement in the words of the position that stands for the answer
     */
    List<DemandReading.Read> asked(Proposition stated) {
        return reading == null ? null : DemandReading.asked(stated, reading);
    }
}
