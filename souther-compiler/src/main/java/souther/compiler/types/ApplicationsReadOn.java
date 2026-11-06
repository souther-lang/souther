package souther.compiler.types;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * The applications of closures a reading of a line was read on, each told by the calls some source
 * wrote that made it.
 *
 * <p>Beside a reading and never in what tells two readings apart. Two applications drawing one
 * line at one place are one reading of it, read on both; what the reading is does not turn on how
 * many applications read it, and a measure counts readings. So readings put together put their
 * applications together, and nothing is chosen between them.
 *
 * <p>Only applications some call a source wrote made. A reading read once — outside every closure,
 * or inside one whose applications are not said — was read on none this says, and is said to be
 * read on none: nothing is made up for an application nobody named.
 *
 * @param each every application, in the order they were met
 */
public record ApplicationsReadOn(Set<AnApplicationOfAClosure> each) {

    /** Read on no application a source's call made. */
    public static final ApplicationsReadOn NONE = new ApplicationsReadOn(Set.of());

    public ApplicationsReadOn {
        Set<AnApplicationOfAClosure> written = new LinkedHashSet<>();
        for (AnApplicationOfAClosure one : each) {
            if (one.isMadeByAWrittenCall()) {
                written.add(one);
            }
        }
        each = Collections.unmodifiableSet(written);
    }

    /** Read on {@code applications}, those some call a source wrote made. */
    public static ApplicationsReadOn of(Collection<AnApplicationOfAClosure> applications) {
        return applications.isEmpty() ? NONE : new ApplicationsReadOn(new LinkedHashSet<>(
                applications));
    }

    /** Read on these and on {@code other}'s. */
    public ApplicationsReadOn and(ApplicationsReadOn other) {
        if (other.each.isEmpty() || each.containsAll(other.each)) {
            return this;
        }
        Set<AnApplicationOfAClosure> both = new LinkedHashSet<>(each);
        both.addAll(other.each);
        return new ApplicationsReadOn(both);
    }

    public boolean isEmpty() {
        return each.isEmpty();
    }

    /**
     * Of one call, over some readings: how many of its applications made some of them, and how
     * many of them some application of it made.
     *
     * <p>Two counts and no relation between them. Two applications reading one line at one place
     * are one reading of two applications, and one application can read several lines.
     *
     * @param call         the call, in the copy of the body it stands in
     * @param applications its applications some of the readings were read on, or inside
     * @param readings     the readings read on one of them, or inside one
     */
    public record OfACall(ACallOfAnOperation call, int applications, int readings) {

        public OfACall {
            Objects.requireNonNull(call, "a call some source wrote");
        }
    }

    /**
     * For each call whose applications made some of {@code readings}, its count of each, in the
     * order the calls are first met.
     *
     * <p>An application of a call is the way to it, the applications around it included
     * ({@link AnApplicationOfAClosure#upTo}): a closure's application inside two applications of
     * the one around it is two applications, and a reading read inside an application of an outer
     * call is a reading of that call too.
     */
    public static List<OfACall> byCall(List<ApplicationsReadOn> readings) {
        Map<ACallOfAnOperation, Set<AnApplicationOfAClosure>> applications = new LinkedHashMap<>();
        Map<ACallOfAnOperation, Integer> read = new LinkedHashMap<>();
        for (ApplicationsReadOn reading : readings) {
            Set<ACallOfAnOperation> calls = new LinkedHashSet<>();
            for (AnApplicationOfAClosure one : reading.each) {
                for (int at = 0; at < one.by().size(); at++) {
                    ACallOfAnOperation call = one.by().get(at).call();
                    applications.computeIfAbsent(call, _ -> new LinkedHashSet<>())
                            .add(one.upTo(at));
                    calls.add(call);
                }
            }
            calls.forEach(call -> read.merge(call, 1, Integer::sum));
        }
        List<OfACall> out = new ArrayList<>();
        applications.forEach((call, made) ->
                out.add(new OfACall(call, made.size(), read.get(call))));
        return out;
    }
}
