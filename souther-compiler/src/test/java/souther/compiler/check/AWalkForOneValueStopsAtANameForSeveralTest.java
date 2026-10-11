package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A walk for one value stops at a name that stands for one of several values, however many it is one
 * of; a walk for every value follows it into each.
 *
 * <p>A name that is one value and a name that is one of several are two answers the environment
 * gives ({@link ValueStanding.Named}), and the difference is not how many values there are. A name
 * one of a single value is still one of them: on another run, or under another narrowing, there
 * could be another, and what holds of it is what holds of the set. Counted afterwards, the set of
 * one would be read as the value.
 */
class AWalkForOneValueStopsAtANameForSeveralTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("probe.walk", "f");
    private static final BindingId ONE_OF_ONE = new BindingId(OWNER, 0);
    private static final BindingId ONE_OF_TWO = new BindingId(OWNER, 1);
    private static final BindingId DENOTES = new BindingId(OWNER, 2);

    private static Core.Int number(long value) {
        return new Core.Int(value, Type.INT, POS);
    }

    private static Core.Read read(BindingId binding) {
        return new Core.Read("n", binding, Type.INT, POS);
    }

    /** An environment answering for three names: one of a single value, one of two, and one that
     *  is a value. With no plurality, the first two are names of nothing it follows. */
    private record Env(boolean plural)
            implements ValueStanding.Names<String, Env> {

        private static final Map<BindingId, List<Core>> SEVERAL = Map.of(
                ONE_OF_ONE, List.of(number(1)),
                ONE_OF_TWO, List.of(number(1), number(2)));

        @Override
        public ValueStanding.ReadThrough<String> readThrough(Core.Read read, String at) {
            return read.binding().equals(DENOTES)
                    ? new ValueStanding.ReadThrough<>(number(7), at) : null;
        }

        @Override
        public List<ValueStanding.ReadThrough<String>> alternativesOf(Core.Read read,
                                                                    String at) {
            List<Core> values = plural ? SEVERAL.get(read.binding()) : null;
            return values == null ? null
                    : values.stream().map(each -> new ValueStanding.ReadThrough<>(each, at))
                            .toList();
        }

        @Override
        public String inside(Core.LetIn li, String at) {
            return at;
        }

        @Override
        public Env oneAtATime() {
            return new Env(false);
        }
    }

    @Test
    void aWalkForOneValueStopsAtANameOneOfASingleValue() {
        Core.Read name = read(ONE_OF_ONE);
        assertSame(name, ValueStanding.one(name, "here", new Env(true)).value(),
                "a name one of a single value is not that value");
    }

    @Test
    void aWalkForOneValueStopsAtANameOneOfTwoValues() {
        Core.Read name = read(ONE_OF_TWO);
        assertSame(name, ValueStanding.one(name, "here", new Env(true)).value());
    }

    @Test
    void aWalkForOneValueFollowsANameThatIsAValue() {
        assertEquals(number(7), ValueStanding.one(read(DENOTES), "here", new Env(true)).value());
    }

    @Test
    void aWalkForEveryValueFollowsANameIntoEachValueItIsOneOf() {
        assertEquals(List.of(number(1)), ValueStanding.of(read(ONE_OF_ONE), "here", new Env(true))
                .stream().map(ValueStanding.Standing::value).toList());
        assertEquals(List.of(number(1), number(2)),
                ValueStanding.of(read(ONE_OF_TWO), "here", new Env(true))
                        .stream().map(ValueStanding.Standing::value).toList());
    }
}
