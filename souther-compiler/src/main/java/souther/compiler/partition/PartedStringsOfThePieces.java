package souther.compiler.partition;

import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.PieceWitness;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The string each piece held to a language is a piece of, and how its pieces were taken, by the
 * piece.
 *
 * <p>A piece is of one string: every statement that holds it to a language says the same of where
 * it comes from. Two that say otherwise are not about one piece, whatever named them alike, and
 * nothing is known of it: it is neither of the strings, and a reader asking is told none.
 */
final class PartedStringsOfThePieces {

    static final PartedStringsOfThePieces NONE = new PartedStringsOfThePieces(Map.of());

    private final Map<PieceWitness, Derivation.APieceInALanguage.PartedString> known;

    private PartedStringsOfThePieces(
            Map<PieceWitness, Derivation.APieceInALanguage.PartedString> known) {
        this.known = known;
    }

    /** What the statements holding pieces to a language say of where the pieces come from. */
    static PartedStringsOfThePieces of(List<Derivation.APieceInALanguage> held) {
        Map<PieceWitness, Derivation.APieceInALanguage.PartedString> known = new HashMap<>();
        Set<PieceWitness> contradicted = new HashSet<>();
        for (Derivation.APieceInALanguage each : held) {
            if (each.parted().isEmpty()) {
                continue;
            }
            Derivation.APieceInALanguage.PartedString said = each.parted().get();
            Derivation.APieceInALanguage.PartedString before =
                    known.putIfAbsent(each.within(), said);
            if (before != null && !before.equals(said)) {
                contradicted.add(each.within());
            }
        }
        known.keySet().removeAll(contradicted);
        return new PartedStringsOfThePieces(Map.copyOf(known));
    }

    /** The string {@code piece} is a piece of, where the statements agree on it. */
    Optional<Derivation.APieceInALanguage.PartedString> of(PieceWitness piece) {
        return Optional.ofNullable(known.get(piece));
    }
}
