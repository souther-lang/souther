package souther.compiler.generated;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Objects;
import java.util.Set;

/**
 * Which behaviors of a module this compile generated an implementation for.
 *
 * <p>The emitter's own decision, kept. A behavior written with a {@code let} body and a {@code >->}
 * composition are emitted as classes that apply them, and a behavior written with neither is emitted
 * as a base for something outside to supply — so what is here is the first kind, and what is not here
 * is a behavior this compile has nothing to run.
 *
 * <p>Read off what the emission put rather than worked out again from how the module is written.
 * Both answers agree today, and that they agree is a fact about one compile rather than a rule: the
 * second reader is what makes them able to disagree, and a reader deciding from the declarations
 * would go on saying a behavior has an implementation after the emitter stopped producing one for it.
 * Not read off the classes either — a name that is not in a loader is a class that could not be
 * reached, which is a failure, and reading membership for it would turn that failure into "nothing
 * applies this", which is not a failure at all.
 *
 * <p><b>Absent is two things and they are named apart.</b> A behavior with no implementation here
 * either was never this compile's to implement, or was and could not be made into one that runs —
 * an implementation whose module holds a body nothing elaborated is emitted for the bodies that may
 * be run, and the rest are its to make and not made. A row about the first is waiting for something
 * to supply the behavior and is right as far as it goes; a row about the second was to be run
 * against this compile's own implementation and could not be. So which of the two it is is carried
 * rather than left to be guessed at: the emitter is what knows, and reading it back off the
 * declarations would answer from what the module says instead of from what was emitted.
 *
 * @param module     the module these behaviors are of
 * @param behaviors  the names it generated an implementation for
 * @param owedButNotMade the names whose implementation was this emission's to make and was not made
 */
public record GeneratedImplementations(String module, Set<String> behaviors,
                                       Set<String> owedButNotMade) {

    /** What this compile came to about one behavior's implementation. */
    public enum Standing {
        /** Emitted here, and a row about the behavior may be run against it. */
        GENERATED,
        /** This compile's to emit and not emitted, so there is nothing here to run it against. */
        OWED_BUT_NOT_MADE,
        /** Never this compile's: something outside supplies the behavior, or nothing does yet. */
        ELSEWHERE
    }

    public GeneratedImplementations {
        Objects.requireNonNull(module, "a manifest says which module it is of");
        Objects.requireNonNull(behaviors, "a manifest says what it implemented, or that it is empty");
        Objects.requireNonNull(owedButNotMade,
                "a manifest says what it owed and did not make, or that it owed nothing");
        // In the order they were emitted. `Set.copyOf` would keep the members and not the order —
        // its iteration order is salted per JVM run — so anything that came to print or compare this
        // would read differently from one run to the next, for no change to the module.
        behaviors = Collections.unmodifiableSet(new LinkedHashSet<>(behaviors));
        owedButNotMade = Collections.unmodifiableSet(new LinkedHashSet<>(owedButNotMade));
        for (String behavior : owedButNotMade) {
            if (behaviors.contains(behavior)) {
                throw new IllegalArgumentException("`" + module + "." + behavior + "` is both"
                        + " emitted here and recorded as not made");
            }
        }
    }

    /**
     * What this compile came to about {@code behavior}'s implementation.
     *
     * <p>The one way to ask. A membership test beside this would answer the question its coarser
     * half asks — whether a class is here — and a reader taking that for the whole of it gives a
     * behavior this compile owed and did not make the answer it gives one nobody owes.
     */
    public Standing standingOf(String behavior) {
        if (behaviors.contains(behavior)) {
            return Standing.GENERATED;
        }
        return owedButNotMade.contains(behavior)
                ? Standing.OWED_BUT_NOT_MADE : Standing.ELSEWHERE;
    }
}
