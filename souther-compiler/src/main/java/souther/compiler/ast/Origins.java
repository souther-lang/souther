package souther.compiler.ast;

/**
 * What a {@link ConstructionOrigin} is, one arm per answer.
 *
 * <p>Here rather than beside the interface because this class is package-private and its members
 * are reached through it: a pass outside this package cannot name an arm, so the only origins there
 * are, are the ones the forms that hold one make. Naming the arms in the interface would make them
 * public — a record's canonical constructor is as accessible as the record — and minting an origin
 * would be back to anyone's.
 */
final class Origins {

    private Origins() {}

    /** {@code origin}, carried into a reader by {@code module}'s published body. */
    static ConstructionOrigin publishedIn(ConstructionOrigin origin, String module) {
        return origin instanceof ByValue ? origin : new Published(module);
    }

    /** {@code origin}, carried into a body by a value that body named. */
    static ConstructionOrigin byValue(ConstructionOrigin origin) {
        return origin instanceof ByValue kept ? kept : ByValue.IT_IS;
    }

    /** A construction written where it stands. */
    record Own() implements ConstructionOrigin {

        static final Own IT_IS = new Own();
    }

    /** A construction carried into a reader by {@code module}'s published body. */
    record Published(String module) implements ConstructionOrigin { }

    /** A construction carried into a body by a value that body named. */
    record ByValue() implements ConstructionOrigin {

        static final ByValue IT_IS = new ByValue();
    }
}
