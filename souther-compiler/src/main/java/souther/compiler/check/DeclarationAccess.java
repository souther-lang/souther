package souther.compiler.check;

/**
 * What a check asks of a declaration it did not write: what the declaration says, which form it
 * is, what it wraps, what each field it reaches holds, and the order a value of it lays those
 * fields out in.
 *
 * <p>Each is its own because each is settled at its own point and moves at its own time, and a
 * check handed the declaration instead would be reading every one of them out of the tree — which
 * is how a body came to be checked again for a declaration that had only moved. The last two are
 * apart for that reason and not only for tidiness: what a field holds and where it stands move at
 * different times, and a mapping does not answer an order.
 *
 * <p>Held together because they travel together, and for no reason beyond that. Nothing here reads
 * one of them off another: a reader handed this asks the ones it uses, and an edit that moves one
 * answer leaves a reader of the others where it was. What the five share is only that the readers
 * carrying one of them carry all five down the same walk, and threaded as five arguments each of
 * those walks said so once per step.
 *
 * <p>The scope is not one of them. What a name written here means is the module's, and these are
 * about a declaration wherever it was written — which is why a reader holds the two side by side
 * rather than one inside the other.
 */
public record DeclarationAccess(PublishedDeclarations published, DeclarationKinds kinds,
                                NewtypeInners inners, EffectiveFieldTypes fieldTypes,
                                FieldLayout layout) {

    public DeclarationAccess {
        if (published == null || kinds == null || inners == null || fieldTypes == null
                || layout == null) {
            throw new IllegalArgumentException("a check reads what the declarations it is written"
                    + " against say, which form each of them is, what each of them wraps, what its"
                    + " fields hold and where they stand, so it is handed somewhere to read every"
                    + " one of them");
        }
    }

    /**
     * The same, for a reader that has not been handed the compilation's answers to what a
     * declaration wraps, what its fields hold and where they stand.
     *
     * <p>Those three are read off {@code symbols} instead, each by the walk that owns the question.
     * What a declaration says and which form it is are still asked for: each sits beside the scope
     * and not inside it, so a reader that wants them from the scope says so where it builds them
     * rather than here. A reader that could have been handed all five and reaches for this is one
     * whose dependency on the declarations nothing has cut.
     */
    public static DeclarationAccess asWritten(Symbols symbols, PublishedDeclarations published,
                                              DeclarationKinds kinds) {
        return new DeclarationAccess(published, kinds, NewtypeInners.asWritten(symbols),
                EffectiveFieldTypes.asWritten(symbols), FieldLayout.asWritten(symbols));
    }
}
