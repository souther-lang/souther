package souther.compiler.flow;

import souther.compiler.inputs.TermPath;
import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * What shows that no value arrives at an arm of a {@code match}.
 *
 * <p>The one answer to whether an arm is entered, with the reason it carries, so that the readers
 * asking it — the one that says whether a run takes the arm and the one that says whether the arm
 * is owed a row — read one decision and not two that could part.
 */
public sealed interface WhyNoValueTakesTheArm {

    /** The value matched on is one the source wrote, and none of the cases it can be is one the arm
     *  takes. */
    record ByWhatIsWritten(List<TypeSymbol> canBe, List<TypeSymbol> cases)
            implements WhyNoValueTakesTheArm {

        public ByWhatIsWritten {
            canBe = List.copyOf(canBe);
            cases = List.copyOf(cases);
        }
    }

    /** What entering the arm states, which the rules and the declarations leave no input to bring
     *  about. */
    record ByWhatItStates(WhyRuledOut why) implements WhyNoValueTakesTheArm {}

    /** The body has no reading of what its arms state, and the rules of the position refuse every
     *  case the arm is written for. */
    record ByTheRulesOfThePosition(TermPath at, List<TypeSymbol> cases)
            implements WhyNoValueTakesTheArm {

        public ByTheRulesOfThePosition {
            cases = List.copyOf(cases);
        }
    }
}
