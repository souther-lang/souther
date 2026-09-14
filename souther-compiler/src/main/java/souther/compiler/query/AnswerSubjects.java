package souther.compiler.query;

import souther.compiler.inputs.Refinement;
import souther.compiler.partition.AnswerDemand;
import souther.compiler.partition.MeasuredInput;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * What a value for one dependency's answer is composed over.
 *
 * <p>One subject where the answer is a type a position stands at, and one per case where it is a
 * union of them. A behavior may answer with an anonymous union — {@code Shipped | NotWritten} —
 * which no parameter names and no position holds, so there is no one subject to compose over; what
 * there is, is a value of one of its cases, and each of those is a type a position stands at.
 *
 * <p><b>Which case is not this type's to choose, and is not chosen here at all.</b> A way that reads
 * the answer as one of them says which ({@link AnswerDemand.ACase}) and leaves one subject; a way
 * that says nothing about it leaves every case a value can be composed over, because that is what
 * the way states. Narrowed to one here, which case a row stands the dependency in with would follow
 * from something about the cases that is not about the model — and what a row goes on to reach
 * follows from the case.
 *
 * @param whole  the subject for the answer as it stands, or null where it is a union
 * @param cases  the cases of a union, in the order they are enumerated in, and empty where the
 *               answer is not one. The order decides which of several equally good rows a reader is
 *               offered and decides nothing about what is searched, every case being searched
 * @param byCase the subject for each case a value can be composed over, which is not every case:
 *               one nothing could be read for has no entry, and is not a case this quietly moves
 *               past
 */
record AnswerSubjects(MeasuredInput whole, List<TypeSymbol> cases,
                      Map<TypeSymbol, MeasuredInput> byCase) {

    AnswerSubjects {
        cases = List.copyOf(cases);
        byCase = Map.copyOf(byCase);
    }

    /**
     * Every subject a value meeting {@code demands} could be composed over, with the demands left
     * for it to meet, and empty where nothing here composes one.
     *
     * <p>Candidates and not a choice. What a way states about the answer is what narrows them: a
     * way naming a case leaves that case alone, and a way saying nothing leaves all of them — so a
     * caller holding several is holding what the model left open rather than a question this
     * declined to answer.
     *
     * <p>Choosing the case of a union answers the demand that named it, so that demand does not
     * travel on: passed to a composer working over the case's own type, it would ask for a
     * narrowing of a position the case does not have.
     */
    List<Feasible> against(List<AnswerDemand> demands) {
        if (whole != null) {
            return List.of(new Feasible(null, whole, demands));
        }
        for (AnswerDemand each : demands) {
            if (each instanceof AnswerDemand.ACase(var _, var _, var steps, var to)
                    && steps.isEmpty() && to instanceof Refinement.SumCase sum) {
                MeasuredInput standing = byCase.get(sum.leaf());
                return standing == null ? List.of()
                        : List.of(new Feasible(sum.leaf(), standing, demands.stream()
                                .filter(left -> left != each).toList()));
            }
        }
        // Nothing says which case, so a value of any of them is a value the way admits, and each of
        // them is a candidate. A way that asks something else of a union answer — its truth, or a
        // comparison over it — is one nothing here composes for: the demand stays in hand, and no
        // value meets it.
        List<Feasible> out = new ArrayList<>();
        for (TypeSymbol each : cases) {
            MeasuredInput standing = byCase.get(each);
            if (standing != null) {
                out.add(new Feasible(each, standing, demands));
            }
        }
        return List.copyOf(out);
    }

    /**
     * One subject a value could be composed over, and what is left for that value to meet.
     *
     * <p>The case is carried beside the subject because it is what tells two candidates for one
     * answer apart. Two askings of one dependency are answered by one value where they are answered
     * by a value of one case, and which case that is is a fact about the candidate rather than
     * about the words the value is printed with.
     *
     * @param caseOfTheAnswer which case of the union this composes a value of, or null where the
     *                        answer is not a union and there is one subject for the whole of it
     */
    record Feasible(TypeSymbol caseOfTheAnswer, MeasuredInput standing,
                    List<AnswerDemand> demands) {}
}
