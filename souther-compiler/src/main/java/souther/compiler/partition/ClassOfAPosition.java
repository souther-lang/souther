package souther.compiler.partition;

import java.util.Comparator;

/**
 * One class of one position: an axis, and which of the classes that axis divides it into.
 *
 * <p>What a row is owed for, and what tells one such thing from every other. The axis names the
 * behavior, so two behaviors dividing their own positions the same way are two of these.
 *
 * <p>Its own type rather than the generator's, because the generator is not what says which classes
 * there are. What a position divides into is the model's answer, read by the partition; a search is
 * one of the readers that asks about it, beside the account that keeps it and the document that
 * publishes it. Held inside the search, the identity every one of them joins on would have been the
 * search's own vocabulary, and an account rooted there says a row is owed for what a search happens
 * to be able to look for.
 */
public record ClassOfAPosition(AxisId at, String classId) {

    /**
     * The words a report writes for the axis, and then what those words are made of, because two
     * axes can be written alike; then the class.
     */
    private static final Comparator<ClassOfAPosition> STEADY = Comparator
            .comparing((ClassOfAPosition each) -> each.at.toString())
            .thenComparing(each -> each.at.behavior())
            .thenComparing(each -> each.at.term())
            .thenComparing(ClassOfAPosition::classId);

    /** The class first, and then the axis by every part of it. */
    private static final Comparator<ClassOfAPosition> BY_CLASS = Comparator
            .comparing(ClassOfAPosition::classId)
            .thenComparing(each -> each.at.toString())
            .thenComparing(each -> each.at.behavior())
            .thenComparing(each -> each.at.term());

    public ClassOfAPosition {
        if (at == null || classId == null) {
            throw new IllegalArgumentException(
                    "a class of a position is some class of some axis: " + at + "/" + classId);
        }
    }

    /**
     * One order for classes, the one a report names a pair in. Every part of a class is compared,
     * so two that are not equal are never tied. Asked for by name and not as a natural order, so
     * that a reader of a sort can see which order it is.
     */
    public static Comparator<ClassOfAPosition> steadyOrder() {
        return STEADY;
    }

    /**
     * The other order a report words classes in: by the class alone, and then by everything else,
     * so that the ids of a pair come out sorted and no two classes that are not equal are tied.
     */
    public static Comparator<ClassOfAPosition> byClassIdOrder() {
        return BY_CLASS;
    }
}
