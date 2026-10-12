package souther.compiler.partition;

import souther.compiler.inputs.InputReading;
import souther.compiler.meaning.Proposition;

import java.util.List;

/**
 * What a statement about an input asks of a value composed for it: the input of the behavior a row
 * is written for, or the input that stands for what a dependency answered.
 *
 * <p>The reading the input was read by, kept beside the subject a value is composed over and not
 * inside it. A statement made over the subject is turned into the demands a row is composed against
 * by the reading a condition of a body is, and what leaves is the demand: nothing that searches for
 * a value reaches the reading, which is what the subject is held apart from it for.
 *
 * <p>Held where the composition is asked and not in any answer: two of these are two readings, and
 * the subject beside it is what says whether two compositions are the same.
 */
public final class StatementsOfAnInput {

    /** For a composition that was handed no reading: a statement it is asked to meet is one it
     *  says it did not compose against. */
    public static final StatementsOfAnInput NONE = new StatementsOfAnInput(null);

    private final InputReading reading;

    private StatementsOfAnInput(InputReading reading) {
        this.reading = reading;
    }

    /** The statements of the input {@code reading} is the reading of. */
    public static StatementsOfAnInput of(InputReading reading) {
        if (reading == null) {
            throw new IllegalArgumentException("statements are asked of the reading of an input");
        }
        return new StatementsOfAnInput(reading);
    }

    /**
     * What {@code stated} asks of a row, or null where there is no reading to ask it of.
     *
     * @param stated a statement in the words of the input this reads
     */
    List<DemandReading.Read> asked(Proposition stated) {
        return reading == null ? null : DemandReading.asked(stated, reading);
    }
}
