package souther.compiler.check;

import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.function.Supplier;

/**
 * The declarations holding one end, worked out at most once.
 *
 * <p>Kept rather than worked out where the value is made, because working them out reads the
 * declaration again once per candidate and most readers of a coordinate's range never ask. What is
 * kept afterwards is the answer and not the work, so one of these answers the same thing however
 * often it is asked and whoever asks first pays.
 *
 * <p>Never handed out on its own. One of these is what an end holds, and a caller that could take
 * it without the end is a caller that will put it beside whatever end it has — which is what
 * {@link NarrowedBounds} exists to stop being possible.
 */
final class Held {

    /** An end nobody is holding, which is what a reading that relates nothing arrives at. */
    static final Held NONE = new Held(List.of());

    private Supplier<List<TypeSymbol.AtModule>> work;
    private List<TypeSymbol.AtModule> found;

    Held(List<TypeSymbol.AtModule> found) {
        this.found = canonical(found);
    }

    Held(Supplier<List<TypeSymbol.AtModule>> work) {
        this.work = work;
    }

    /** These and {@code also} together, worked out only if either is ever asked for. */
    static Held both(Held one, Held also) {
        return new Held(() -> {
            List<TypeSymbol.AtModule> out = new java.util.ArrayList<>(one.names());
            out.addAll(also.names());
            return out;
        });
    }

    synchronized List<TypeSymbol.AtModule> names() {
        if (found == null) {
            found = canonical(work.get());
            work = null;
        }
        return found;
    }

    /**
     * The declarations in one order and each of them once.
     *
     * <p>Several of these are one answer, and an order read off the walk that collected them would
     * make two readings of one edge into two answers. The same order {@link FieldDomains} settles a
     * single reading's names in, because these are the same names met.
     */
    private static List<TypeSymbol.AtModule> canonical(List<TypeSymbol.AtModule> found) {
        return found.stream().distinct().sorted().toList();
    }
}
