package souther.compiler.check;

import souther.compiler.types.BindingId;

/**
 * The subject a place is, for a test that enters bindings by hand.
 *
 * <p>{@link Denotations} is handed what each binding's subject is rather than working it out, so a
 * test standing in for the walk has to answer the same question the walk does. Asked of {@link
 * Terms}, which is the one thing that says which value something is — a test minting an identity of
 * its own would be testing against a second answer.
 */
final class AsPlaces {

    private AsPlaces() {
    }

    static FactSubject of(BindingId binding) {
        return new Terms(Symbols.none()).placeSubject(binding);
    }

    static Term term(BindingId binding) {
        return new Terms(Symbols.none()).placeTerm(binding);
    }
}
