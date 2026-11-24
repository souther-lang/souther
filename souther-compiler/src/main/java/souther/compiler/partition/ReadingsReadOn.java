package souther.compiler.partition;

import souther.compiler.types.ApplicationsReadOn;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Which applications of the closures a body's comparisons stand in read each line they drew, by
 * the line's origin: the comparison's copy, the part and case of it, and the line, which is what
 * tells two readings of a line apart.
 *
 * <p>Beside the origins and not in them. Every reader that tells two readings apart, files one,
 * or keeps one of two alike asks the origin; which applications read a line is no part of any of
 * those answers, and is asked of the origin here and nowhere else. A line narrowed by a
 * declaration is the line its bound is ({@link LineOrigin.NarrowedOrigin}), and is read on what
 * that line is.
 *
 * @param byOrigin the applications that read the line of each origin, none of them empty
 */
public record ReadingsReadOn(Map<LineOrigin, ApplicationsReadOn> byOrigin) {

    /** No line read on an application of a closure. */
    public static final ReadingsReadOn NONE = new ReadingsReadOn(Map.of());

    public ReadingsReadOn {
        Map<LineOrigin, ApplicationsReadOn> kept = new LinkedHashMap<>();
        byOrigin.forEach((origin, by) -> {
            if (!by.isEmpty()) {
                kept.put(origin, by);
            }
        });
        byOrigin = Collections.unmodifiableMap(kept);
    }

    /** The applications that read the line of {@code origin}: none where none did, or where no
     *  comparison drew it. */
    public ApplicationsReadOn of(LineOrigin origin) {
        return switch (origin) {
            case LineOrigin.ComparisonOrigin comparison ->
                    byOrigin.getOrDefault(comparison, ApplicationsReadOn.NONE);
            case LineOrigin.NarrowedOrigin narrowed -> of(narrowed.bound());
            case LineOrigin.InvariantOrigin _, LineOrigin.EnsuresOrigin _ ->
                    ApplicationsReadOn.NONE;
        };
    }

    /** What a reading of a body is told, origin by origin, as it makes each. */
    static final class Taking {

        private final Map<LineOrigin, ApplicationsReadOn> byOrigin = new LinkedHashMap<>();

        /** The line of {@code origin}, read by {@code by} as well as by whatever read it
         *  before: one line drawn twice is read on what read either. */
        void read(LineOrigin origin, ApplicationsReadOn by) {
            byOrigin.merge(origin, by, ApplicationsReadOn::and);
        }

        ReadingsReadOn taken() {
            return new ReadingsReadOn(byOrigin);
        }
    }
}
