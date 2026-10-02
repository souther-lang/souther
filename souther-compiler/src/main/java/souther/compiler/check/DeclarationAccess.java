package souther.compiler.check;

/**
 * What a check asks of a declaration it did not write: what the declaration says, which form it
 * is, what it wraps, what each field it reaches holds, the order a value of it lays those fields
 * out in, and which enumerations list it among their cases.
 *
 * <p>Each is its own because each is settled at its own point and moves at its own time, and a
 * check handed the declaration instead would be reading every one of them out of the tree — which
 * is how a body came to be checked again for a declaration that had only moved. The last two are
 * apart for that reason and not only for tidiness: what a field holds and where it stands move at
 * different times, and a mapping does not answer an order.
 *
 * <p>Held together because they travel together, and for no reason beyond that. Nothing here reads
 * one of them off another: a reader handed this asks the ones it uses, and an edit that moves one
 * answer leaves a reader of the others where it was. What the six share is only that the readers
 * carrying one of them carry all six down the same walk, and threaded as six arguments each of
 * those walks said so once per step.
 *
 * <p>The scope is not one of them. What a name written here means is the module's, and these are
 * about a declaration wherever it was written — which is why a reader holds the two side by side
 * rather than one inside the other.
 */
public record DeclarationAccess(PublishedDeclarations published, DeclarationKinds kinds,
                                NewtypeInners inners, EffectiveFieldTypes fieldTypes,
                                FieldLayout layout, EnumerationListings enumerations) {

    /** Nothing declared anywhere — for a reading over primitives, which asks of no declaration. */
    public static final DeclarationAccess NONE = new DeclarationAccess(PublishedDeclarations.NONE,
            DeclarationKinds.NONE, NewtypeInners.NONE, EffectiveFieldTypes.NONE, FieldLayout.NONE,
            EnumerationListings.NONE);

    public DeclarationAccess {
        if (published == null || kinds == null || inners == null || fieldTypes == null
                || layout == null || enumerations == null) {
            throw new IllegalArgumentException("a check reads what the declarations it is written"
                    + " against say, which form each of them is, what each of them wraps, what its"
                    + " fields hold, where they stand and which enumerations list it, so it is"
                    + " handed somewhere to read every one of them");
        }
    }

    /**
     * The same, for a reader that has not been handed the compilation's answers to what a
     * declaration wraps, what its fields hold, where they stand and which enumerations list it.
     *
     * <p>Those four are read off {@code symbols} instead, each by the walk that owns the question.
     * What a declaration says and which form it is are still asked for: each sits beside the scope
     * and not inside it, so a reader that wants them from the scope says so where it builds them
     * rather than here. A reader that could have been handed all six and reaches for this is one
     * whose dependency on the declarations nothing has cut.
     */
    public static DeclarationAccess asWritten(Symbols symbols, PublishedDeclarations published,
                                              DeclarationKinds kinds) {
        return new DeclarationAccess(published, kinds, NewtypeInners.asWritten(symbols),
                EffectiveFieldTypes.asWritten(symbols), FieldLayout.asWritten(symbols),
                EnumerationListings.asWritten(symbols, kinds, published));
    }

    /**
     * The same answers, with what a declaration says read off {@code said} instead — and which
     * enumerations list a value read off it too, each time it is asked.
     *
     * <p>For a reader that takes a declaration out of what is said, which is how what a declaration
     * says comes to be made. What lists a value is read off what the sums say, so an answer kept
     * anywhere else would be read past that.
     */
    public DeclarationAccess saying(PublishedDeclarations said, Symbols symbols) {
        return new DeclarationAccess(said, kinds, inners, fieldTypes, layout,
                EnumerationListings.asWritten(symbols, kinds, said));
    }
}
