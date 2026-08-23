package souther.compiler.check;

import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.List;

/**
 * What one clause of a declaration guarantees of the value at one position, read as an assumption.
 *
 * <p>The answer a type gives about a value, and nothing about who asked. A walk seeding a path and a
 * recipe settling a choice want the same thing of a declaration, and what they do with it differs;
 * this is the thing, and what is done with it is the consumer's. So nothing here mentions a
 * {@link Known}, a path, or what is being measured.
 *
 * <p>{@code owed} and {@code quantified} are one answer and not two lists to be read side by side.
 * A quantified relation is one this very clause states of the elements of a container it names, so
 * pairing them by index somewhere downstream is an account of the pairing that can come apart from
 * the reading that made it.
 *
 * @param rule      which rule of the model this is — the clause of the declaration's invariant, and
 *                  not where this reading met it ({@link RuleRef}). Beside the answer rather than
 *                  inside it: what a type guarantees is the same whether or not anybody is filing
 *                  questions under rules, and only a consumer that does ({@link
 *                  InvariantChecker.Gathering}) reads this
 * @param clause    the clause as it stands at this position, with the declaration's fields rebased
 *                  onto the value they are about
 * @param owed      what reading that clause came to: a relation, a fact, both, or that it could not
 *                  be read at all. Not narrowed to a numeric constraint — a clause states what it
 *                  states, and a reader wanting only the numbers can ask {@link Predicates.Owed}
 *                  for them
 * @param quantified what the clause states of every element of a container it names
 * @param parts      what each part of the clause came to as it was read. A conjunction is read a
 *                   conjunct at a time, and what each conjunct came to is the reading's own answer
 *                   about that conjunct — kept here because asking it again afterwards is a second
 *                   reader, and the two agree only until somebody changes one of them
 */
record TypeGuarantee(RuleRef.Invariant rule, Core clause, Predicates.Owed owed,
                     List<Quantified> quantified, List<Part> parts) {

    TypeGuarantee {
        quantified = List.copyOf(quantified);
        parts = List.copyOf(parts);
    }

    /**
     * What this guarantee comes to as relations.
     *
     * <p>What a clause states of the value, and what is known of the size of any container it names.
     * Both hold of the value itself, which is what makes them recordable where a range could not be
     * ({@link NumericConstraint}).
     *
     * <p>A clause this reading could not state as a relation is not here, and neither is one it
     * read as a fact. Under-answering costs precision; answering with something else would not be
     * sound.
     */
    List<NumericConstraint> relations() {
        List<NumericConstraint> out = new ArrayList<>();
        for (Predicates.Part each : owed.parts()) {
            if (!(each instanceof Predicates.Part.Carried carried)) {
                continue;
            }
            Predicates.Clause clause = carried.clause();
            out.addAll(clause.known());
            if (clause.numeric() != null) {
                out.add(clause.numeric());
            }
        }
        return List.copyOf(out);
    }

    /** What one part of a clause came to, beside the part it was read from. */
    record Part(Core part, Predicates.Owed owed) {}
}
