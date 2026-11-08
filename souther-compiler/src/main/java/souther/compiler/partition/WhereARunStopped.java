package souther.compiler.partition;

import souther.compiler.execute.RunStop;
import souther.compiler.source.SourceId;

import java.util.Comparator;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * Where a composed row's run stopped without answering, with the source its place is written in.
 *
 * <p>What the generated code and the runtime said, and which of this compilation's sources the
 * module they named is written in — asked of the compilation where the run is read, since the code
 * that stopped knows a module and not a source. None where the stop names no module, or where no
 * source of this compilation declares the one it names.
 *
 * @param stop   what the run said of where it stopped
 * @param source the source the place is written in, where this compilation has it
 */
public record WhereARunStopped(RunStop stop, Optional<SourceId> source) {

    /**
     * These in a steady order, which two of them are equal in only where they are equal: where the
     * run stopped ({@link RunStop#IN_A_STEADY_ORDER}), then the source it is written in, none
     * first.
     */
    public static final Comparator<WhereARunStopped> IN_A_STEADY_ORDER =
            Comparator.comparing(WhereARunStopped::stop, RunStop.IN_A_STEADY_ORDER)
                    .thenComparing(each -> each.source().map(SourceId::value).orElse(null),
                            Comparator.nullsFirst(Comparator.naturalOrder()));

    public WhereARunStopped {
        Objects.requireNonNull(stop, "a run stopped somewhere");
        Objects.requireNonNull(source, "a place is in one of these sources or in none");
    }

    /** Two lists of these, one place at a time and then by how many: a steady order over lists
     *  that is one only where the lists are equal. */
    public static int compare(List<WhereARunStopped> one, List<WhereARunStopped> other) {
        for (int i = 0; i < Math.min(one.size(), other.size()); i++) {
            int byPlace = IN_A_STEADY_ORDER.compare(one.get(i), other.get(i));
            if (byPlace != 0) {
                return byPlace;
            }
        }
        return Integer.compare(one.size(), other.size());
    }
}
