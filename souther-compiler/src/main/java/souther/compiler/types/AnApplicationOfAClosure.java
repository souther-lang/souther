package souther.compiler.types;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * One application of a closure, told by the calls some source wrote that made it: for each closure
 * it stands inside whose call some source wrote, that call and which of its applications it is,
 * the outermost first.
 *
 * <p>Every call on the way, and not the innermost alone. A closure inside another is applied once
 * inside each application of the one around it, and counted from nought inside each, so its first
 * application inside the outer one's first and its first inside the outer one's second are two
 * applications with one ordinal.
 *
 * <p>Calls no source wrote are not on the way: an application made only by those is told by no
 * call ({@link #OF_NO_CALL_WRITTEN}), and an author is told nothing of it.
 *
 * @param by each call some source wrote that made it, and which of that call's applications it is
 *           inside, the outermost first
 */
public record AnApplicationOfAClosure(List<Made> by) {

    /** An application no call some source wrote made. */
    public static final AnApplicationOfAClosure OF_NO_CALL_WRITTEN =
            new AnApplicationOfAClosure(List.of());

    public AnApplicationOfAClosure {
        by = List.copyOf(by);
    }

    /**
     * One application a call makes of a closure: the call, and which of its applications it is,
     * counting from nought in the order a run makes them.
     */
    public record Made(ACallOfAnOperation call, int ordinal) {

        public Made {
            Objects.requireNonNull(call, "an application is made by some call");
            if (ordinal < 0) {
                throw new IllegalArgumentException("applications are counted from nought: "
                        + ordinal);
            }
        }
    }

    /** An application made inside this one, by {@code made}. */
    public AnApplicationOfAClosure inside(Made made) {
        List<Made> deeper = new ArrayList<>(by);
        deeper.add(made);
        return new AnApplicationOfAClosure(deeper);
    }

    /** Whether some call a source wrote made it. */
    public boolean isMadeByAWrittenCall() {
        return !by.isEmpty();
    }

    /**
     * The application of the call at {@code at} on the way to this one, the calls before it
     * included: the first {@code at + 1} of {@link #by}.
     */
    public AnApplicationOfAClosure upTo(int at) {
        return new AnApplicationOfAClosure(by.subList(0, at + 1));
    }
}
