package souther.compiler.meaning;

import souther.compiler.inputs.AnEvaluation;
import souther.compiler.types.ValueName;

import java.util.List;

/**
 * What a dependency answered, as a row can pin it.
 *
 * <p><b>One evaluation, which is what tells one of these from another.</b> A dependency is the
 * outside world, and two calls of one need not answer alike whatever they were handed: keyed by
 * what it was applied to, {@code nextId() > 5} written twice would be one question, and the way
 * through the first denied and the second held would be no way at all. A name given the answer is
 * the same evaluation ({@link AnEvaluation}), and so the same answer however often it is read.
 *
 * <p>What a row does about two evaluations of one dependency is the row's question and not this
 * one's: it stands the dependency in with one value, so a way needing the two to answer apart is a
 * way that wants a table, which is something composing a row comes to and not something the reading
 * of the body decides by running them together.
 *
 * <p>The arguments are what it was asked about, which a row pinning the answer and a report
 * naming it say. Two spellings of one argument are one question asked; what an argument has to be is
 * known and not controlled — a number the model settles is as much a question asked as a position a
 * row writes at — which is {@link DecisionArgument}'s, beside the subjects rather than among them.
 *
 * @param evaluation which call of which dependency
 * @param arguments  what it was applied to, in the order the declaration takes them
 */
public record InjectedAnswer(AnEvaluation evaluation, List<DecisionArgument> arguments) {

    public InjectedAnswer {
        if (evaluation == null || arguments == null) {
            throw new IllegalArgumentException(
                    "an answer of a dependency is one call of it, applied to something");
        }
        arguments = List.copyOf(arguments);
    }

    /** Which behavior the row stands in for, named as the provisioning names it. */
    public ValueName.Behavior dependency() {
        return evaluation.dependency();
    }

    /**
     * What this answer is, as an identity spells it.
     *
     * <p>The behavior under the module that declares it, what it was applied to, and which call it
     * is. Two modules may declare behaviors of one name, and two calls of one behavior are two
     * answers; a spelling that left either off would have one column for two — and, where an order
     * is taken over these, would settle that order by which of them a reader happened to meet.
     */
    public String spelled() {
        ValueName.Behavior dependency = dependency();
        StringBuilder out = new StringBuilder(dependency.module()).append('.')
                .append(dependency.name()).append('(');
        for (int i = 0; i < arguments.size(); i++) {
            out.append(i == 0 ? "" : ", ").append(arguments.get(i).spelled());
        }
        return out.append(')').append(evaluation.spelled()).toString();
    }

    @Override
    public String toString() {
        return spelled();
    }
}
