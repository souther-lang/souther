package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.types.ValueName;

import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The witness laws and the facts they are read in place of say the same thing about the same
 * operations, for as long as both are declared.
 *
 * <p>Two statements of one operation are two places a reader can be told different things. While
 * readers move from the dependency a closure's truth decides and the statement of a predicate of
 * every element onto the witness law, each operation one of them names is held to say, through the
 * law, what the older fact said: a closure deciding the result's truth or emptiness is a witness
 * on that side answering a truth, and a predicate of every element is a result that fails where
 * some element's answer does.
 */
class AWitnessSaysWhatTheDependencyBesideItSaysTest {

    private static final BoundOperationFacts FACTS = DefaultBoundOperationFacts.get();

    @Test
    void aClosureDecidingASideIsAWitnessOnThatSideAnsweringATruth() {
        Set<String> decided = new TreeSet<>();
        Set<String> witnessedByATruth = new TreeSet<>();
        for (ValueName operation : DefaultStdlib.get().entries().keySet()) {
            ElementWitness witness = FACTS.resultHasAnElementWitness(operation);
            for (AnswerAspect aspect : AnswerAspect.values()) {
                BoundOperationFact.TurnsOnWhetherAnArgumentHolds turns =
                        FACTS.turnsOnWhetherAnArgumentHolds(operation, aspect);
                if (turns != null && witness != null
                        && turns.argument().equals(witness.closure())) {
                    decided.add(operation + " " + aspect);
                } else if (turns != null && Combinators.of(operation) != null) {
                    decided.add(operation + " " + aspect + " with no witness");
                }
            }
            // The dependency says a truth decides a truth or an emptiness; a result coming out as
            // holding a value is a side it has no word for, so a law about one has nothing beside it.
            if (witness != null && witness.ofTheClosure().aspect() == AnswerAspect.TRUTH
                    && witness.result().aspect() != AnswerAspect.PRESENCE) {
                witnessedByATruth.add(operation + " " + witness.result().aspect());
            }
        }
        assertEquals(witnessedByATruth, decided);
    }

    @Test
    void aPredicateOfEveryElementFailsWhereSomeElementFails() {
        Set<String> every = new TreeSet<>();
        Set<String> failsWhereOneFails = new TreeSet<>();
        SideAnswered fails = new SideAnswered(AnswerAspect.TRUTH, false);
        for (ValueName operation : DefaultStdlib.get().entries().keySet()) {
            if (FACTS.statesItsPredicateOfEveryElement(operation)) {
                every.add(operation.toString());
            }
            ElementWitness witness = FACTS.resultHasAnElementWitness(operation);
            if (witness != null && witness.result().equals(fails)
                    && witness.ofTheClosure().equals(fails)) {
                failsWhereOneFails.add(operation.toString());
            }
        }
        assertEquals(failsWhereOneFails, every);
    }
}
