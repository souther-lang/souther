package souther.compiler.partition;

import souther.compiler.inputs.TermPath;

import java.util.List;

/**
 * A row as a test hands it to a form: read at its positions or over a run, and never one element
 * at a time, which only a quantity that is no form asks of it.
 */
public abstract class AnObservationOfAForm implements BorderQuantity.Observation {

    @Override
    public final WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath container) {
        throw new AssertionError("a form is read at its positions and not element by element");
    }
}
