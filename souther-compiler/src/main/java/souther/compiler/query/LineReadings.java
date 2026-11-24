package souther.compiler.query;

import java.util.List;

/**
 * One behavior's lines, one entry per reading of one.
 *
 * <p>A type of its own so that a reading and a line are not the same thing to hold. Both are lists
 * of the same assessment, and what tells them apart is only whether the readings of one line have
 * been brought together yet — written as one type, a caller could hand either to anything and the
 * order the two are asked in would be kept by nothing but a comment.
 *
 * <p>What the order is about: a reading is reached under its caller's own conditions, and that is
 * what a row for its line is composed against ({@link Coverages#searched}). Once the readings are
 * one, the conditions belong to whichever of them the fold kept. So a search takes these and gives
 * these back, {@link Coverages#merged} takes these and gives back the lines, and nothing goes the
 * other way round: asking for a fold and then searching what came out of it does not compile.
 *
 * <p>And what the rows fix of the weights of each computation the model's rules cut at several
 * places. A computation is one however many borders cut it, so what the rows fix of its weights
 * is a fact about it and belongs to no one reading of a border.
 *
 * @param each  the readings, in the order they were made
 * @param tilts what the rows fix of the weights of each computation, which is every one the
 *              partition left owing weights
 */
public record LineReadings(List<BorderAssessment> each, List<TiltOfADerivedValue> tilts) {

    public LineReadings {
        each = List.copyOf(each);
        tilts = List.copyOf(tilts);
    }

    public LineReadings(List<BorderAssessment> each) {
        this(each, List.of());
    }
}
