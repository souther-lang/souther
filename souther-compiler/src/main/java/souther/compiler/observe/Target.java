package souther.compiler.observe;

/**
 * What an {@link Incompleteness} is about, as the thing itself rather than as a name and a word for
 * what kind of name it is.
 *
 * <p>A scope and a string are a product, and what they stand for is a sum: each kind of subject is a
 * different thing and answers "is this behavior inside it" a different way. Held as a product, a
 * subject can be spelled for one scope and read for another, and a scope can be added that no reader
 * answers for — which is what happened to {@code POSITION}. Nothing wrote one into the list a report
 * reads, so the branch that would have answered for it was never reached, and the fallback answered
 * true for every behavior in the module.
 *
 * <p>A position knows which behavior it is in, so it says so. Reading that back out of
 * {@code submit/request.kind} would be putting the same distinction back into a string.
 *
 * <p>Deliberately not {@code AxisId}. That is the partition's identity for an axis and it lives
 * there; this is what a reason needs to say whose measurement it counts against. The two happen to
 * be spelled alike and are not the same thing, and the conversion belongs on the partition's side,
 * where the axis is.
 */
public sealed interface Target {

    /** What a report prints, and what two reasons are compared on. */
    String subject();

    /** Which kind of name {@link #subject} is. */
    Incompleteness.Scope scope();

    /**
     * The behavior this is about, where the thing it names is inside one. Empty otherwise.
     *
     * <p>One answer to that question and not three. It was asked as a scope test beside a subject
     * comparison, twice, and as a containment question a third time, and a scope that answered the
     * first two differently from the third is how a position came to count against a module.
     *
     * <p>This much and no more. Whether a behavior is inside a <em>source</em> is not something a
     * source id says — it is a fact about the compilation that wrote the rows — so nothing here
     * answers it. What a reason counts against is {@link Incompleteness#countsAgainst}'s, where the
     * reading that settles it can be stated.
     */
    java.util.Optional<String> onlyBehavior();

    /** One behavior. Only that behavior's measures are affected. */
    record OfBehavior(String behavior) implements Target {

        @Override
        public String subject() {
            return behavior;
        }

        @Override
        public Incompleteness.Scope scope() {
            return Incompleteness.Scope.BEHAVIOR;
        }

        @Override
        public java.util.Optional<String> onlyBehavior() {
            return java.util.Optional.of(behavior);
        }
    }

    /**
     * One source, named. What it holds is not part of it: a source id is a file, and which
     * behaviors wrote rows in it is the compilation's answer rather than the name's.
     */
    record OfSource(String sourceId) implements Target {

        @Override
        public String subject() {
            return sourceId;
        }

        @Override
        public Incompleteness.Scope scope() {
            return Incompleteness.Scope.SOURCE;
        }

        @Override
        public java.util.Optional<String> onlyBehavior() {
            return java.util.Optional.empty();
        }
    }

    /** The module, and so everything in it. */
    record OfModule(String module) implements Target {

        @Override
        public String subject() {
            return module;
        }

        @Override
        public Incompleteness.Scope scope() {
            return Incompleteness.Scope.MODULE;
        }

        @Override
        public java.util.Optional<String> onlyBehavior() {
            return java.util.Optional.empty();
        }
    }

    /** A position inside one behavior's input — a path through a value, and the behavior it is in. */
    record AtPosition(String behavior, String path) implements Target {

        @Override
        public String subject() {
            return behavior + "/" + path;
        }

        @Override
        public Incompleteness.Scope scope() {
            return Incompleteness.Scope.POSITION;
        }

        @Override
        public java.util.Optional<String> onlyBehavior() {
            return java.util.Optional.of(behavior);
        }
    }

    /**
     * The target a scope and a subject stand for, where the subject is a name.
     *
     * <p>{@code POSITION} is not among them: its subject is two names and cannot be recovered from
     * one. Producers of a position use {@link Incompleteness#atPosition} and pass both.
     */
    static Target of(Incompleteness.Scope scope, String subject) {
        return switch (scope) {
            case BEHAVIOR -> new OfBehavior(subject);
            case SOURCE -> new OfSource(subject);
            case MODULE -> new OfModule(subject);
            case POSITION -> throw new IllegalArgumentException(
                    "a position needs the behavior it is in: " + subject);
        };
    }
}
