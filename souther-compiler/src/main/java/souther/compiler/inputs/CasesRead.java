package souther.compiler.inputs;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.SequencedMap;

/**
 * Every case of one sum, and what became of each.
 *
 * <p>The whole list, because what is asked of it is asked of all of them at once: a sum has a value
 * wherever any case does, so a reader holding some of the cases can say nothing. Assembled from the
 * roots a walk opened and the cases it turned back at, the list would be one fact in three places —
 * and the case nobody thought to look for would be the one that says the model has a value.
 *
 * <p>In the order the cases are declared, which is the order a reason about them reads in.
 *
 * @param sum      where the sum stands
 * @param outcomes what became of each of its cases
 */
record CasesRead(TermPath sum, SequencedMap<Refinement, CaseOutcome> outcomes) {

    CasesRead {
        outcomes = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(outcomes));
    }
}
