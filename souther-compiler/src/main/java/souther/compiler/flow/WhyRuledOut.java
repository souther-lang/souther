package souther.compiler.flow;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.Rel;
import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * What was shown when a way was ruled out: the fact about the input that leaves no value behind it.
 *
 * <p>Carried with the answer because a reader that drops an arm on it owes an author the reason, and
 * the reason is what was proved here. Worked out again by the reader, it would be a second reading of
 * the same statement, free to disagree with the one that decided.
 */
public sealed interface WhyRuledOut {

    /** What is stated never comes out the way asked, whatever the input. */
    record ItNeverComesOutSo() implements WhyRuledOut {}

    /**
     * The declaration of the position states every case a value there can be, and none of them is
     * the way asked: none of {@code asked} where {@code among}, nothing but {@code asked} where not.
     *
     * @param declared every case the position's type holds, in the order it declares them
     * @param asked    the cases the statement names
     */
    record TheDeclarationLeavesNone(TermPath at, List<TypeSymbol> declared,
                                    List<TypeSymbol> asked, boolean among)
            implements WhyRuledOut {

        public TheDeclarationLeavesNone {
            declared = List.copyOf(declared);
            asked = List.copyOf(asked);
            if (declared.isEmpty() || asked.isEmpty()) {
                throw new IllegalArgumentException(
                        "a declaration leaving no case asked, with no case declared or asked");
            }
        }
    }

    /** The position's type holds the cases the way needs and its rules refuse every one of them. */
    record TheRulesRefuseEveryCase(TermPath at, List<Case> refused) implements WhyRuledOut {

        public TheRulesRefuseEveryCase {
            refused = List.copyOf(refused);
            if (refused.isEmpty()) {
                throw new IllegalArgumentException("every case refused, of no cases");
            }
        }
    }

    /** The rules leave the numbers {@code relation} is over no value at which it comes out as
     *  {@code asked} says. */
    record TheNumbersLeaveNone(Relation relation, Rel asked) implements WhyRuledOut {}

    /** The container at {@code container} holds nothing on any input, so no element of it meets
     *  anything. */
    record NothingIsHeldIn(TermPath container) implements WhyRuledOut {}

    /** Each of several alternatives was ruled out, each for its own reason. */
    record EveryWay(List<WhyRuledOut> each) implements WhyRuledOut {

        public EveryWay {
            each = List.copyOf(each);
            if (each.isEmpty()) {
                throw new IllegalArgumentException("every way ruled out, of no ways");
            }
        }
    }
}
