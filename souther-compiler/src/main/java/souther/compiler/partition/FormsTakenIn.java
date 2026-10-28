package souther.compiler.partition;

import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * What the region of one reading of the input answers to a form taken in, kept for that reading.
 *
 * <p>A form coming out a way is asked of the region before anything is taken in, and the answer
 * is a function of the region, the form and the way alone. The comparisons of an input are few
 * and each is read for every proposition that states it, so asked each time the region is made to
 * order the same terms again; kept here, each form and way is asked once. What is kept is the
 * region's answer and not a read made of it: a read is told where it was read off by the node
 * that holds it, so one handed to two propositions would be told for both.
 *
 * <p>Of one reading, which is held and asked for: the region is the reading's, and an answer
 * under one region is no answer under another ({@link InputReading#derived}).
 */
final class FormsTakenIn {

    private final SearchRegion region;
    private final Map<AForm, SearchRegion.Assumption> assumptions = new ConcurrentHashMap<>();

    private FormsTakenIn(InputReading read) {
        this.region = read.quantities().region();
    }

    /** What the forms taken in over {@code read} came to, kept for that reading. */
    static FormsTakenIn of(InputReading read) {
        return read.derived(FormsTakenIn.class, FormsTakenIn::new);
    }

    /** What {@code form} coming out {@code rel} comes to in the region. */
    SearchRegion.Assumption assuming(LinearForm<NumericTerm> form, Rel rel) {
        return assumptions.computeIfAbsent(new AForm(form, rel),
                asked -> region.assuming(asked.form(), asked.rel()));
    }

    private record AForm(LinearForm<NumericTerm> form, Rel rel) {}
}
