package souther.compiler.publish;

import souther.compiler.partition.InputUse;

/**
 * What a document calls whether anything a behavior states reads a position of its input.
 *
 * <p>An enum for the reason {@link NotMeasuredWord} is one: the shipped schema names these words in
 * its own file and is held against this.
 */
public enum InputUseWord {

    /** Something the behavior states reads the value, and a row is owed at each class. */
    READ,

    /** Nothing the behavior states reads the value, and no row is owed at any class. */
    NOT_READ,

    /** Whether anything reads the value is not known, and a row is owed at each class. */
    NOT_KNOWN;

    /** The word for {@code use}. */
    public static InputUseWord of(InputUse use) {
        return switch (use) {
            case InputUse.Read _ -> READ;
            case InputUse.NotRead _ -> NOT_READ;
            case InputUse.NotKnown _ -> NOT_KNOWN;
        };
    }
}
