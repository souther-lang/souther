package souther.compiler.partition;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.TermPath;

import java.util.List;

/**
 * Where a rule about a value that stands at no one position is owed the sentence, and which
 * sentence, read off an answer of where the value came from ({@link PathResolution}).
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
    static OwedWhereItCameFrom ofSeveral(PathResolution cameFrom) {
        return switch (cameFrom) {
            case PathResolution.MayStandAt(var among) -> new OwedWhereItCameFrom(among,
                    new BlockReason.RuleAboutAnElementOfSeveralContainers());
            case PathResolution.MadeOf made -> new OwedWhereItCameFrom(made.places(),
                    new BlockReason.RuleAboutADerivedValue());
            case PathResolution.At _, PathResolution.NotAPosition _ -> null;
        };
    }
}
