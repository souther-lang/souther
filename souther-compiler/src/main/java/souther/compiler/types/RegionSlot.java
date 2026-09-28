package souther.compiler.types;

import souther.compiler.SettledAnswer;

import java.util.List;
import java.util.Optional;

/**
 * Which way out of a construct an evaluation region is, said in words the source settles.
 *
 * <p>A construct that opens regions opens more than one, and what tells them apart is which slot of
 * it each is. Every arm here is fixed by what the author wrote and by nothing a pass did: the arms
 * of an {@code if} are two, an attempted construction's refused arms are told by the clause each
 * answers for, and a {@code match} arm by the case names it was written for. None is a position in
 * a walk, and none is the order the arms were met in.
 *
 * <p>A slot is not where a construct stands. It says which of the regions its construct opened is
 * meant, and the construct is the {@link MaterialisationSite.Slot} it is paired with.
 */
public sealed interface RegionSlot extends SettledAnswer {

    /** The arm an {@code if} takes when its condition holds. */
    record IfThen() implements RegionSlot { }

    /** The arm an {@code if} takes when it does not. */
    record IfElse() implements RegionSlot { }

    /** The arm of an attempted construction that runs when the value was built. */
    record ConstructedThen() implements RegionSlot { }

    /**
     * The arm of an attempted construction that runs when it was refused.
     *
     * <p>Told by the clause it answers for, empty for the arm that answers for any. The arms are a
     * lookup by clause and not a sequence, so the order they were written in says nothing here.
     */
    record ConstructedElse(Optional<String> clause) implements RegionSlot {

        public ConstructedElse {
            if (clause == null) {
                throw new IllegalArgumentException(
                        "a refused arm answers for one clause or for any: " + clause);
            }
        }
    }

    /**
     * The arm of a {@code match} written for these cases.
     *
     * <p>Told by the names as the author wrote them. A case named in two arms of one {@code match}
     * is refused before an expansion reads it ({@code CasePartition#namedTwiceIn}), so the names
     * tell the arms of one match apart without saying which was written first.
     */
    record MatchCase(List<String> caseTypes) implements RegionSlot {

        public MatchCase {
            if (caseTypes == null || caseTypes.isEmpty()) {
                throw new IllegalArgumentException(
                        "a match arm is written for some case: " + caseTypes);
            }
            caseTypes = List.copyOf(caseTypes);
        }
    }

    /** What stands on the right of {@code &&} or {@code ||}: reached for some of what reaches the
     *  left. */
    record ShortCircuitRight() implements RegionSlot { }

    /** The element a comprehension writes for each item. */
    record ComprehensionElement() implements RegionSlot { }

    /** The guard of a comprehension the author wrote {@code index}th among its guards. */
    record ComprehensionGuard(int index) implements RegionSlot {

        public ComprehensionGuard {
            if (index < 0) {
                throw new IllegalArgumentException("a guard is one of those written: " + index);
            }
        }
    }
}
