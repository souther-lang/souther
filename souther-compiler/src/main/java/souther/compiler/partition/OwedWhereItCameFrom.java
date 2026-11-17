package souther.compiler.partition;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.MadeFrom;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.ValuesAt;

import java.util.ArrayList;
import java.util.List;

/**
 * Where a rule about a value that stands at no one position is owed the sentence, and which
 * sentence, read off an answer of where the value came from ({@link MadeFrom}).
 *
 * <p>The one place an answer of several becomes a report, for the reader of a comparison and the
 * reader of a string's rule alike. Each decided it for itself, and an answer one of them learned
 * the other sent to a reading of something else. The two sentences are different: a value that
 * is what stands at one of several places is about the input at whichever of them the run is in,
 * and a value made of several places is one somebody computed from them, at every one.
 *
 * @param places every place the rule is owed the sentence at
 * @param why    the sentence
 */
record OwedWhereItCameFrom(List<TermPath> places, BlockReason.RuleReadingStopped why) {

    OwedWhereItCameFrom {
        places = List.copyOf(places);
        if (places.isEmpty()) {
            throw new IllegalArgumentException("a rule is owed the sentence somewhere: " + why);
        }
    }

    /**
     * What {@code cameFrom} says of a value that came from several places, or null where it says
     * one place, or none: whether and where a rule about those is said is each reader's own, since
     * a value that came from one place is read through the operation that made it.
     */
    static OwedWhereItCameFrom ofSeveral(MadeFrom cameFrom) {
        return switch (cameFrom) {
            case MadeFrom.FromOneOf(var among) -> new OwedWhereItCameFrom(among,
                    new BlockReason.RuleAboutAnElementOfSeveralContainers());
            case MadeFrom.FromEvery made -> new OwedWhereItCameFrom(made.places(),
                    new BlockReason.RuleAboutADerivedValue());
            case MadeFrom.FromOne _, MadeFrom.FromNothing _ -> null;
        };
    }

    /**
     * What a value that may stand at one of several places is owed, said by where it stands and by
     * where it came from together, or null where it stands at no one of several.
     *
     * <p>The places it may stand at are the position's, with their fields. What it was made out of
     * beyond those is the origin's ({@link MadeFrom#placesBeyond}): a name a block was handed over
     * a container the input holds and over one made of another is at the first on one run and made
     * of the second on the next, and the rule is owed at both. Taken from the position alone, the
     * second is left out.
     */
    static OwedWhereItCameFrom ofSeveral(ValuesAt stands, MadeFrom cameFrom) {
        if (!(stands instanceof ValuesAt.MayStandAt(var among))) {
            return null;
        }
        List<TermPath> places = new ArrayList<>(among);
        for (TermPath beyond : cameFrom.placesBeyond(stands)) {
            if (!places.contains(beyond)) {
                places.add(beyond);
            }
        }
        return new OwedWhereItCameFrom(places,
                new BlockReason.RuleAboutAnElementOfSeveralContainers());
    }
}
