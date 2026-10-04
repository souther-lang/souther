package souther.compiler.check;

import souther.compiler.types.TypeKey;

/**
 * What a check asks of a declaration it did not write: what the declaration says, which form it
 * is, what it wraps, what each field it reaches holds, the order a value of it lays those fields
 * out in, what a value of a sum can be, which enumerations list it among their cases, and where a
 * report points at what a value name reaches.
 *
 * <p>Each is its own because each is settled at its own point and moves at its own time, and a
 * check handed the declaration instead would be reading every one of them out of the tree — which
 * is how a body came to be checked again for a declaration that had only moved. What a field holds
 * and where it stands are apart for that reason and not only for tidiness: the two move at
 * different times, and a mapping does not answer an order. What a sum can be and what lists a
 * value are apart for the same reason: one is answered for a sum and the other for a module, and
 * a sum of the module moving reaches only the readers of that sum through the first.
 *
 * <p>Held together because they travel together, and for no reason beyond that. Nothing here reads
 * one of them off another: a reader handed this asks the ones it uses, and an edit that moves one
 * answer leaves a reader of the others where it was. What they share is only that the readers
 * carrying one of them carry all of them down the same walk, and threaded as separate arguments each
 * of those walks said so once per step. Where a value name's reach is, is one of them for that
 * reason: a report that points at one is made deep in the walk that types a call.
 *
 * <p>The scope is not one of them. What a name written here means is the module's, and these are
 * about a declaration wherever it was written — which is why a reader holds the two side by side
 * rather than one inside the other.
 */
public record DeclarationAccess(PublishedDeclarations published, DeclarationKinds kinds,
                                NewtypeInners inners, EffectiveFieldTypes fieldTypes,
                                FieldLayout layout, SumCases sums,
                                EnumerationListings enumerations,
                                ReachedValueLocations reachedLocations) {

    /** Nothing declared anywhere — for a reading over primitives, which asks of no declaration. */
    public static final DeclarationAccess NONE = new DeclarationAccess(PublishedDeclarations.NONE,
            DeclarationKinds.NONE, NewtypeInners.NONE, EffectiveFieldTypes.NONE, FieldLayout.NONE,
            SumCases.NONE, EnumerationListings.NONE, ReachedValueLocations.NOT_HELD);

    public DeclarationAccess {
        if (published == null || kinds == null || inners == null || fieldTypes == null
                || layout == null || sums == null || enumerations == null
                || reachedLocations == null) {
            throw new IllegalArgumentException("a check is handed somewhere to ask every question"
                    + " about the declarations this carries");
        }
    }

    /**
     * The same, for a reader that has not been handed the compilation's answers to what a
     * declaration wraps, what its fields hold, where they stand, what a value of a sum can be and
     * which enumerations list it.
     *
     * <p>Those are read off {@code symbols} and the declarations instead, each by the walk that
     * owns the question. What a declaration says and which form it is are still asked for: each
     * sits beside the scope and not inside it, so a reader that wants them from the scope says so
     * where it builds them rather than here. A reader that could have been handed all of them and
     * reaches for this is one whose dependency on the declarations nothing has cut.
     *
     * <p>Where a value name's reach is, is not read off anything: such a reader types what the
     * check accepted, and only a report the check would have made first asks it.
     */
    public static DeclarationAccess asWritten(Symbols symbols, PublishedDeclarations published,
                                              DeclarationKinds kinds) {
        SumCases sums = SumCases.asWritten(kinds, published);
        return new DeclarationAccess(published, kinds, NewtypeInners.asWritten(symbols),
                EffectiveFieldTypes.asWritten(symbols), FieldLayout.asWritten(symbols), sums,
                EnumerationListings.asWritten(symbols, kinds, sums),
                ReachedValueLocations.NOT_HELD);
    }

    /**
     * The same answers, with the one declaration whose meaning is being made taken out of what the
     * declarations say.
     *
     * <p>A clause of a declaration names other declarations — which case a comparison is over, what
     * a sum an operand is of divides into — and those are looked up like anywhere else. The one
     * that cannot be looked up is the declaration whose meaning is being made: asking would be
     * asking for the answer being worked out, and answering nothing would say instead that nothing
     * declares it, which every clause of it would then be reported under.
     *
     * <p>Only that one answer is narrowed. What a value of a sum can be and which enumerations list
     * a value are the two other answers read off what declarations say, and both are kept as they
     * were handed: each reads what sums say, asked only of a declaration its form says is a sum,
     * and a sum's meaning reads no clause. The only meaning made by reading clauses is a product's,
     * so neither answer is made out of the declaration being made. Where a value name's reach is,
     * is kept too: it is no answer about what any declaration says.
     */
    DeclarationAccess making(TypeKey made) {
        PublishedDeclarations besidesIt = declaration -> made.equals(declaration)
                ? PublishedDeclarations.THE_ONE_THAT_MAKES_THEM.of(declaration)
                : published.of(declaration);
        return new DeclarationAccess(besidesIt, kinds, inners, fieldTypes, layout, sums,
                enumerations, reachedLocations);
    }
}
