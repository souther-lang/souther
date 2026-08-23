package souther.compiler.check;

import souther.compiler.core.Core;

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
 */
record TypeGuarantee(RuleRef.Invariant rule, Core clause, Predicates.Owed owed,
                     List<Quantified> quantified) {

    TypeGuarantee {
        quantified = List.copyOf(quantified);
    }
}
