package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhyUnread;

import java.util.List;

/**
 * Which parts a fork's answer turns on, each with the expression it was read off.
 *
 * <p>What the fork tests states a proposition ({@link Pullback}), carried back through what the
 * library says its operations do and nowhere else: {@code List.any(p, xs)} turns on what {@code p}
 * answers, and so does whether {@code List.filter(p, xs)} holds anything, while whether
 * {@code List.map(p, xs)} does turns on {@code xs} alone. The parts are the ones that proposition
 * is made of, read once, so a reader asking who owns a part and a reader asking what the fork
 * states are asking about the same parts.
 *
 * <p><b>The parts and not whether one of them was found.</b> Which of them a reader owns is a
 * question about each of them: a closure answering {@code p.age > 18 && List.contains(0, p.tags)}
 * states a comparison and something nothing here reads, and the fork around the operation states
 * the second whoever owns the first.
 *
 * <p><b>Only what can vary, read off the proposition.</b> A part that comes out the same whatever
 * the input is an answer and not a question, so nobody owns it and it is not offered — and whether
 * a part varies is a question about where it stands in what the fork states, not about the part on
 * its own ({@link Pullback.Pulled#turnsOn}).
 */
final class WhatAForkTests {

    private WhatAForkTests() {}

    /**
     * What was read of the parts an answer turns on.
     *
     * <p>A proposition a reading stopped in at a figure states the parts it got to, and where it
     * got to is where the figure ran out and not what the answer turns on. A part it holds may be
     * one the complete reading would not hold in that form, and a part it lacks was not found
     * absent. Only a complete reading therefore offers its parts: that no part is left, and which
     * parts are, are both questions the figure took away. A part nothing reads is a part of the
     * answer all the same, and does not make it incomplete.
     */
    sealed interface PartsRead {

        /**
         * No figure stopped the proposition, so these are all the parts the answer turns on.
         * That is all this says: a part another reason left unread is among them, and nothing
         * here is a proof that the answer was worked out.
         */
        record Complete(List<Denotation> parts, ReadAsPieces pieces) implements PartsRead {

            public Complete {
                parts = List.copyOf(parts);
            }
        }

        /** The proposition was stopped in at a figure, for these, and says nothing of which parts
         *  there are: the parts it got to are not offered. */
        record Incomplete(List<WhyUnread> stoppedFor) implements PartsRead {

            public Incomplete {
                stoppedFor = List.copyOf(stoppedFor);
            }
        }
    }

    /**
     * What the reading of an atom proved of the pieces of a string.
     *
     * <p>A part of the atom that is the container whose pieces were walked is stated by the
     * comparison that was read of one piece only where the truth proved that the value is one of
     * the pieces ({@link Derivation.SomePieceEqualling}): that some piece is the value is the
     * existential statement the comparison draws its relation from, and the denial of a comparison
     * of the piece with the value is not it.
     *
     * @param containers the containers the truth proved some piece equal to a value of
     */
    record ReadAsPieces(List<Denotation> containers) {

        ReadAsPieces {
            containers = List.copyOf(containers);
        }
    }

    /** What was read of the parts the truth of {@code atom} turns on. */
    static PartsRead partsRead(Core atom, WhatNamesStandFor names) {
        Pullback.Pulled truth =
                WhatConditionsState.of(names.read()).truth(atom, names.reads(), names.read());
        List<WhyUnread> stops = Proposition.stopsIn(truth.proposition());
        if (stops.stream().anyMatch(why -> why.figure().isPresent())) {
            return new PartsRead.Incomplete(stops);
        }
        List<Pullback.Leaf> turnsOn = truth.turnsOn();
        return new PartsRead.Complete(turnsOn.stream().map(Pullback.Leaf::from).toList(),
                new ReadAsPieces(turnsOn.stream().filter(leaf -> isAmongThePieces(leaf.part()))
                        .map(Pullback.Leaf::from).toList()));
    }

    /** Whether {@code part} is the relation of a value being one of the pieces of a string. */
    private static boolean isAmongThePieces(Proposition part) {
        if (part instanceof Proposition.Some(var _, var ofTheElement, var _, var _)) {
            return isAmongThePieces(ofTheElement);
        }
        return part instanceof Proposition.Compared(Relation.Affine(var form, var _), var _, var _)
                && form.coefs().keySet().stream().anyMatch(Quantity.IsAmongThePieces.class::isInstance);
    }
}
