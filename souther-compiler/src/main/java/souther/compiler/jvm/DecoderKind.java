package souther.compiler.jvm;

/**
 * Which of a type's three decoders is meant. Each is emitted as its own class and each has its own
 * spelling, so the kind is part of what identifies the class — {@code $Dec}, {@code $DecJson},
 * {@code $DecRecord}.
 *
 * <p>The codec generator switches on the same three values for things that are not names at all: the
 * field accessor to call, the leaf decoders to reach for, whether an object guard is written. Those
 * are its own, and its own enum keeps them; this one says only what the three decoders are called,
 * which is the ABI's to say.
 */
public enum DecoderKind {

    /** The neutral decoder, over values already in Souther's own shapes: {@code $Dec}. */
    VALUE,

    /** The decoder over parsed JSON: {@code $DecJson}. */
    JSON,

    /** The decoder over a jOOQ record: {@code $DecRecord}. */
    RECORD
}
