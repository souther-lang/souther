package souther.compiler.types;

/**
 * What a type goes by where a union carries it, which is three answers and not two.
 *
 * <p>A member the compiler could not work out a type for and a member whose type cannot be one are
 * not the same finding, and a reader that gets one answer for both reports the second sentence about
 * the first: that a name denoting nothing is not the kind of thing an arm can name. Kept apart here
 * so that a reader has to say which of the two it is acting on, and a reader added later cannot
 * decide it by not noticing.
 *
 * <p>A question about a type and not about where one was written, so it is answered beside the type
 * rather than by whoever is reading a declaration. What a written type comes to and what a union may
 * carry are two questions, and the second one is this; asking it here is what keeps the reading of a
 * written type from being the only place that knows the rule.
 */
public sealed interface UnionMember {

    /** The case name this member is written and dispatched under. */
    record Named(TypeSymbol name) implements UnionMember {}

    /** A type no arm can name, so no union can carry it. */
    record NotAMember() implements UnionMember {}

    /** A member resting on a name that denotes nothing, reported where that name was written. */
    record NoType() implements UnionMember {}

    NotAMember NOT_A_MEMBER = new NotAMember();
    NoType NO_TYPE = new NoType();

    /**
     * The case name a union member goes by: a data type's own name, or the name a primitive is
     * written under in a match arm ({@code Int} in {@code Int | NoAnswer}).
     *
     * <p>A member has to be nominal and has to tell itself apart from the other members at run time,
     * because that is what a {@code match} arm and a Java {@code switch} both dispatch on. A
     * collection fails the second: its type argument is erased, so {@code List<Order>} and
     * {@code List<Item>} are one runtime type and no arm could choose between them. An
     * {@code Option} and a function fail it the same way. That they also have no arm form to write
     * is the surface showing the same fact.
     */
    static UnionMember of(Type m) {
        // The type that absorbs stands where the compiler could not work one out. It is not a shape
        // this question has an answer about, and reading it as one is how the name that denotes
        // nothing came to be reported a second time as a member an arm could not name.
        if (m instanceof Type.Erroneous) {
            return NO_TYPE;
        }
        if (m instanceof Type.Ref r) {
            return new Named(r.name());
        }
        // Exhaustive over the primitives rather than a chain of comparisons, and reading the one
        // spelling table rather than repeating it. A chain answers "not a member" for a primitive
        // added later without asking anyone, and that answer is the truth about Raw and about
        // nothing else.
        if (m instanceof Type.Prim p) {
            return switch (p) {
                case INT, STRING, BOOL, DECIMAL, RATIONAL, DATE, TIME, DATETIME, INSTANT ->
                        new Named(TypeSymbol.primitive(p.shown()));
                case RAW -> NOT_A_MEMBER;
            };
        }
        return NOT_A_MEMBER;
    }
}
