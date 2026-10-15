package souther.compiler.proof;

import souther.compiler.core.TheWalk;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.ToIntFunction;

/**
 * That every call of the walk ends, proved from its body and from what reading an element at an
 * index answers.
 *
 * <p>The walk's body says it calls itself only where reading the element at its index answers
 * something, and then with the next index and the same list, and answers its seed otherwise
 * ({@link TheWalk}). What reading an element answers is a law of a kernel: it holds a value exactly
 * where the index is no less than nought and less than the list's length. So where the walk calls
 * itself the list is longer than the index, and the length less the index — a whole number — is at
 * least one and is one less on the call. A whole number that is at least one at every call and
 * falls by one at each cannot fall for ever, so the walk ends, from any index it starts at.
 *
 * <p>This leans on the law and on the shape of the body and on nothing about the walk ending: the
 * shape is read with no question of termination ({@code stdlib.TheWalksBody}), and the law is an
 * axiom about the kernel, held to what it computes by running it.
 */
public final class TheWalkEnds {

    /** The two numbers the law is read over. */
    private enum Number {
        /** The index the element is read at. */
        INDEX,
        /** How many the list holds. */
        LENGTH
    }

    private TheWalkEnds() {}

    /**
     * Whether {@code presence}, the law of when reading an element answers something — over an
     * index at argument {@code index} and a list at argument {@code list}, as {@code positionOf}
     * reads an argument's place — proves that where the walk calls itself the list is longer than
     * the index.
     */
    public static <A> boolean proved(OperationLaw<A> presence, int index, int list,
                                     ToIntFunction<A> positionOf) {
        if (!(presence instanceof OperationLaw.Observation<A>(AnswerAspect aspect,
                LawProposition<A> holds)) || aspect != AnswerAspect.PRESENCE) {
            return false;
        }
        Map<Number, Granularity> whole = Map.of(Number.INDEX, Granularity.DISCRETE,
                Number.LENGTH, Granularity.DISCRETE);
        NumericDomain<Number> where = NumericDomain.top(Enum::compareTo);
        where = where.assume(LinearForm.atom(Number.LENGTH), Rel.GE, whole);
        for (LawProposition<A> part : parts(holds)) {
            if (!(part instanceof LawProposition.Compared<A>(LinearForm<LawNumber<A>> form,
                    Rel states))) {
                return false;
            }
            LinearForm<Number> read = over(form, index, list, positionOf);
            if (read == null) {
                return false;
            }
            where = where.assume(read, states, whole);
        }
        // The length less the index, less one: no less than nought is the length beyond the index.
        LinearForm<Number> beyond = new LinearForm<>(ExactRatio.of(-1), Map.of(
                Number.LENGTH, ExactRatio.ONE, Number.INDEX, ExactRatio.of(-1)));
        return !where.isBottom() && where.entails(beyond, Rel.GE);
    }

    /** The statements a conjunction is made of, or the one statement it is. */
    private static <A> List<LawProposition<A>> parts(LawProposition<A> holds) {
        return holds instanceof LawProposition.All<A>(List<LawProposition<A>> parts)
                ? parts : List.of(holds);
    }

    /** {@code form} over the index and the length, or null where it is over anything else. */
    private static <A> LinearForm<Number> over(LinearForm<LawNumber<A>> form, int index, int list,
                                               ToIntFunction<A> positionOf) {
        Map<Number, ExactRatio> coefs = new LinkedHashMap<>();
        for (Map.Entry<LawNumber<A>, ExactRatio> term : form.coefs().entrySet()) {
            Number number = switch (term.getKey()) {
                case LawNumber.AnArgument<A>(A argument)
                        when positionOf.applyAsInt(argument) == index -> Number.INDEX;
                case LawNumber.SizeOf<A>(LawSubject.Argument<A>(A argument))
                        when positionOf.applyAsInt(argument) == list -> Number.LENGTH;
                default -> null;
            };
            if (number == null || coefs.containsKey(number)) {
                return null;
            }
            coefs.put(number, term.getValue());
        }
        return new LinearForm<>(form.constant(), coefs);
    }
}
