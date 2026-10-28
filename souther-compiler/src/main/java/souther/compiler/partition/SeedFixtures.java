package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.Optional;

/**
 * A value some row of a behavior observed, written as a fixture another behavior's row can carry.
 *
 * <p>The way {@link ObservedFixtures} writes every value that was built, offered to the callers
 * outside this package that hold an observation and need a row's worth of text from it. Nothing
 * here decides whether the value suits the position it is put at: that is the candidate check's.
 */
public final class SeedFixtures {

    private SeedFixtures() {}

    /**
     * {@code value}, observed at a position of type {@code type}, written as a fixture — or
     * nothing where it cannot be written, which says nothing about the value.
     */
    public static Optional<FixtureTemplate> written(ObservedValue value, Type type,
                                                    RuleReadingContext reading) {
        return ObservedFixtures.of(value, type, reading)
                instanceof ObservedFixtures.Writing.Written<FixtureTemplate>(
                        FixtureTemplate fixture) ? Optional.of(fixture) : Optional.empty();
    }
}
