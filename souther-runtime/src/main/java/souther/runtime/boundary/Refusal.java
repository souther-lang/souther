package souther.runtime.boundary;

import org.jspecify.annotations.Nullable;
import souther.runtime.InvariantFailure;
import souther.runtime.PersistentVector;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * Why a decode refused the value at a path: one of seven things, each carrying what a reader of it
 * needs to say it (spec {@code [#what-a-refusal-says]}).
 *
 * <p>Which of the seven, and what it carries, is decided by the derived decoder and by nothing that
 * read the input or reports the refusal. No message is part of a refusal; where one carries a
 * {@code reason}, it is the language's own account of what the value is, which a reporter may say
 * or may say in its own words.
 */
public sealed interface Refusal {

    /** Where in the input the refused value is. */
    Path path();

    /** The position requires a value and the input has none there. */
    record Absent(Path path) implements Refusal {
        public Absent {
            Objects.requireNonNull(path);
        }
    }

    /**
     * The input holds a value the position does not read.
     *
     * @param expected what the position reads, in the language's words
     * @param found what the input held instead, or null where nothing more than that it is not
     *     {@code expected} is said
     * @param reason why the value is not one, in the language's words
     */
    record NotOfItsKind(Path path, String expected, @Nullable String found, String reason)
            implements Refusal {
        public NotOfItsKind {
            Objects.requireNonNull(path);
            Objects.requireNonNull(expected);
            Objects.requireNonNull(reason);
        }
    }

    /**
     * A discriminator's tag, or an enumeration's name, that no case answers to.
     *
     * @param names the case names, in code point order
     * @param written the name the input wrote
     */
    record NotOneOfTheNames(Path path, List<String> names, String written) implements Refusal {
        public NotOneOfTheNames {
            Objects.requireNonNull(path);
            names = PersistentVector.from(names);
            Objects.requireNonNull(written);
        }
    }

    /**
     * Text the position reads by a form of the language's, which the text is not in.
     *
     * @param form which form: {@code text}, {@code date}, {@code time}, {@code dateTime} or
     *     {@code instant}
     * @param reason what the text does that the form does not allow, in the language's words
     */
    record NotInItsForm(Path path, String form, String reason) implements Refusal {
        public NotInItsForm {
            Objects.requireNonNull(path);
            Objects.requireNonNull(form);
            Objects.requireNonNull(reason);
        }
    }

    /** A map's key that, once decoded, is a key the map already holds. */
    record OneKeyTwice(Path path) implements Refusal {
        public OneKeyTwice {
            Objects.requireNonNull(path);
        }
    }

    /**
     * A newtype's clause the boundary states as a constraint, which the value breaks.
     *
     * @param name which constraint: {@code minLength}, {@code maxLength}, {@code length},
     *     {@code pattern}, {@code min}, {@code max}, {@code positive}, {@code nonNegative},
     *     {@code nonEmpty}, {@code minSize}, {@code maxSize}, {@code size} or {@code unique}. The
     *     set grows as the checker learns to state more clauses exactly.
     * @param data the constraint's bound and what the value was found to be, as plain values:
     *     names, numbers, strings and lists of them, in the order the constraint states them and
     *     iterated in that order, so a library whose messages take their arguments by position can
     *     place those of a constraint it does not know
     */
    record Constraint(Path path, String name, Map<String, Object> data) implements Refusal {
        public Constraint {
            Objects.requireNonNull(path);
            Objects.requireNonNull(name);
            data = Collections.unmodifiableMap(new LinkedHashMap<>(data));
        }
    }

    /**
     * Any other clause the value breaks.
     *
     * @param failure the type and the clause, as the data's checked construction answers for the
     *     same value
     */
    record Clause(Path path, InvariantFailure failure) implements Refusal {
        public Clause {
            Objects.requireNonNull(path);
            Objects.requireNonNull(failure);
        }
    }
}
