package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.inputs.TermPath;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

/**
 * What one parameter's value hands on to the containers of the parameters composed after it, out
 * of what building it came to.
 *
 * <p>Read off what was built, where something built it. Between what a row writes and the value a
 * behavior is handed are the decoders and whatever the module states — a value written by its name
 * is the value the module gives that name — so what stands at a position of it is the boundary's
 * to say, and the same for a value written by name and a value composed here. What the row writes
 * there is all there is only where nothing built it, and a position it does not write is then
 * nothing to hand over.
 *
 * <p>Decided here and once, for every way a parameter is written. Asked at each, the two readings
 * part: a value composed was read off what was built while a value written by name was read off
 * its text, and a field the name stands for was nothing a container could be handed.
 */
final class HandedOn {

    /** What building a parameter's value came to, as what it hands on. */
    sealed interface Came {

        /** The model refused the value. */
        record Refused(String why) implements Came {}

        /** What stands at each position handed on. */
        record Values(Map<TermPath, FixtureTemplate> at) implements Came {

            public Values {
                at = Map.copyOf(at);
            }
        }

        /** The value stands, and what is to be handed on out of it is nothing this can write. */
        record NotWritable(String why) implements Came {}
    }

    /**
     * What a value built as {@code built} hands on at {@code read}.
     *
     * @param written what the row writes at each position it writes one at, which is what is
     *                handed on where nothing built the value. Asked for only then, since working
     *                it out may mean composing each position again
     */
    static Came of(Generator.CandidateCheck.Built built,
                   Supplier<Map<TermPath, FixtureTemplate>> written,
                   Set<TermPath> read, BehaviorInputs inputs, RuleReadingContext reading) {
        return switch (built) {
            case Generator.CandidateCheck.Built.Refused(String why) -> new Came.Refused(why);
            case Generator.CandidateCheck.Built.Value(var observed) ->
                    switch (ObservedFixtures.at(inputs, observed, read, reading)) {
                        case ObservedFixtures.Writing.Written<Map<TermPath, FixtureTemplate>>(
                                var at) -> new Came.Values(at);
                        case ObservedFixtures.Writing.NotWritable<Map<TermPath, FixtureTemplate>>(
                                String why) -> new Came.NotWritable(why);
                    };
            case Generator.CandidateCheck.Built.NothingBuiltIt _ -> {
                Map<TermPath, FixtureTemplate> writes = written.get();
                Map<TermPath, FixtureTemplate> out = new LinkedHashMap<>();
                for (TermPath each : read) {
                    FixtureTemplate value = writes.get(each);
                    if (value == null) {
                        yield new Came.NotWritable("a container is handed the value at `" + each
                                + "`, which the row does not write, and nothing built the value"
                                + " to say what stands there");
                    }
                    out.put(each, value);
                }
                yield new Came.Values(out);
            }
        };
    }

    private HandedOn() {}
}
