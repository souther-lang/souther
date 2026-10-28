package souther.compiler.partition;

import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;

/**
 * Whether the region of one reading of the input takes a form in, kept for that reading.
 *
 * <p>A form coming out a way is asked of the region before anything is taken in, and whether the
 * region takes it in, and why not where it does not, is a function of the region, the form and the
 * way alone. The comparisons of an input are few and each is read for every proposition that states
 * it, so asked each time the region is made to order the same terms again; kept here, each form and
 * way is asked once. What is kept is the refusal or none, and not the region that took the form in:
 * a reader that wants that region asks for it, and one that wants to know whether holds no region
 * for every form it asked about.
 *
 * <p>Of one reading, which is held and asked for: the region is the reading's, and an answer
 * under one region is no answer under another ({@link InputReading#derived}).
 */
final class FormsTakenIn {

    private final SearchRegion region;
    private final Map<AForm, Optional<SearchRegion.Refusal>> refusals = new ConcurrentHashMap<>();

    private FormsTakenIn(InputReading read) {
        this(read.quantities().region());
    }

    FormsTakenIn(SearchRegion region) {
        this.region = region;
    }

    /** Whether the forms taken in over {@code read} are taken in, kept for that reading. */
    static FormsTakenIn of(InputReading read) {
        return read.derived(FormsTakenIn.class, FormsTakenIn::new);
    }

    /** Why the region does not take {@code form} in coming out {@code rel}, or nothing where it does. */
    Optional<SearchRegion.Refusal> refusalOf(LinearForm<NumericTerm> form, Rel rel) {
        return refusals.computeIfAbsent(new AForm(form, rel),
                asked -> switch (region.assuming(asked.form(), asked.rel())) {
                    case SearchRegion.Assumption.Taken _ -> Optional.empty();
                    case SearchRegion.Assumption.Refused(var why) -> Optional.of(why);
                });
    }

    private record AForm(LinearForm<NumericTerm> form, Rel rel) {}
}
