package souther.compiler.check;

import souther.compiler.types.Type;

/**
 * What a declared fact requires of a position in the signature it names.
 *
 * <p>A closed vocabulary, so that requiring something of a position is choosing from it. Written as
 * a {@code Predicate<Type>} the caller handed over, the condition and its name came from the caller
 * too: {@link OperationFactBinder} named a projection's closure by writing
 * {@code type -> type instanceof Type.FnOf} where the call was made, said "no requirement" as
 * {@code type -> true}, and borrowed the two classifications that had been written inside
 * {@link Question} for the rest. Each of those is a classification answered inside a consumer of the
 * answer, which is the defect #1056 removed twice over and this closes the route to (#1059).
 *
 * <p><b>A requirement names a condition; it does not own the answer to one.</b> Each constant below
 * delegates to whatever owns the classification it names, and a constant added is a constant whose
 * owner has been decided. A requirement may read a {@link Type} constructor itself only where the
 * constructor is the whole of the condition, which is why {@link #CLOSURE} stands out: there is no
 * table behind {@code FnOf} to disagree with, and a second answer to what one is cannot be written.
 * The day a requirement wants a condition assembled here out of several, what it wants is an owner.
 *
 * <p>What is asked of a type, and not what is asked of a signature. That two positions stand at one
 * type is a condition no constant here could answer, because nothing about a type on its own decides
 * it; {@link OperationFactBinder} states that one where it holds a shift and both ends are known,
 * and holds the position itself to {@link #ANY}.
 *
 * <p>Not read by {@link Question}, which reads the owners directly. The two sides ask the same
 * things of a type, but this is the vocabulary of one of them — what a fact requires of a
 * declaration — and a range is not a requirement. Read by both, the names here would stop meaning
 * what a fact demands and become somewhere to put a type predicate, which is the shape of the
 * defect rather than the fix.
 */
enum TypeRequirement {

    /** A kind of number the domain relates arithmetically ({@link NumericAnswers#isANumber}). */
    NUMBER("a number"),

    /** A type whose values count to a number, which is wider than being one ({@link Carrier}). */
    COUNTED("something that counts to a number"),

    /** A construction holding elements a rule can speak of ({@link Type#elementOfAContainer}). */
    CONTAINER("a container"),

    /** A function, which is what a rule about a projection or a step is written over. */
    CLOSURE("a closure"),

    /**
     * Nothing about what stands there.
     *
     * <p>A statement and not a gap: the fact names an argument, so the argument has to be one the
     * operation takes, and the rest of the holding says so. What the fact says of it — which of two
     * a positive answer calls the greater — is true of values of any type, so there is nothing about
     * the type to require. {@code admits} answers true for every type, today and after: a
     * requirement that came to answer false for some of them would be a different requirement.
     */
    ANY("any type");

    private final String required;

    TypeRequirement(String required) {
        this.required = required;
    }

    /** Whether {@code type} is what this requires. */
    boolean admits(Type type) {
        return switch (this) {
            case NUMBER -> NumericAnswers.isANumber(type);
            case COUNTED -> Carrier.countsToANumber(type);
            case CONTAINER -> Type.elementOfAContainer(type) != null;
            case CLOSURE -> type instanceof Type.FnOf;
            case ANY -> true;
        };
    }

    @Override
    public String toString() {
        return required;
    }
}
