package souther.compiler.query;

import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.partition.StoodInAnswer;

import java.util.List;
import java.util.Objects;

/**
 * What tells one piece of work from another among the rows a run offers.
 *
 * <p>The row as a person is handed it: the behavior it is written under and the values it is written
 * with, in the form they will be written in. A candidate is composed once per thing it is owed for
 * and the positions that thing does not name hold whatever the row has to hold, so two of them come
 * out as one piece of work — and what a reader would otherwise be pasting twice is one row here.
 *
 * <p><b>What is written, and not what the values are — except where the generator wrote one value
 * two ways.</b> A value the module states is composed into a row by its name, by a spread over its
 * name, and written out where a run read it back; those are one value in three spellings that the
 * generator itself chose, and no person would write them as three rows. Their identity is {@link
 * FixtureTemplate#meaning}, the value written out as the module's own decoder built it. Any other
 * template means its own spelling, so two rows of one behavior that mean the same thing and were
 * written two ways by two authors or two paths stay two rows, each answering what it was composed
 * for. That is the direction to be wrong in: a person reads the row, and an identity over every
 * value would need something none of them has — a fixture carries the position it was parsed at
 * and the path it was constructed through, neither of which is what a reader is looking at.
 *
 * <p>Under one behavior, because a row is written in one behavior's terms. The same values written
 * for two behaviors are two rows in two blocks, and a key that left the behavior out would join them
 * into one piece of work nobody can write.
 *
 * <p><b>And what it stands the dependencies in with.</b> A row of a behavior that decides on what
 * one answers is written with the answer beside the values, and two rows that write one set of
 * values under two answers are two pieces of work that go two different ways. Left out, the second
 * would be joined onto the first and a person would be handed one row said to answer both.
 *
 * <p>What a reader is shown is {@link #written}, from whichever spelling was composed first; the
 * identity is {@link #meant}, and {@link #equals} and {@link #hashCode} are over it.
 *
 * @param behavior the behavior the row is written under
 * @param written  one value per parameter, as the source an author is handed
 * @param meant    one value per parameter, written out, which two spellings of one value share
 * @param stoodIn  what each asking of a dependency is answered with, as the source says it
 */
public record RowKey(String behavior, List<String> written, List<String> meant,
                     List<String> stoodIn) {

    public RowKey {
        written = List.copyOf(written);
        meant = List.copyOf(meant);
        stoodIn = List.copyOf(stoodIn);
        if (behavior == null) {
            throw new IllegalArgumentException("a row is written under some behavior");
        }
        if (meant.size() != written.size()) {
            throw new IllegalArgumentException("a row means as many values as it writes");
        }
    }

    /** A row whose values mean what they are written as. */
    public RowKey(String behavior, List<String> written, List<String> stoodIn) {
        this(behavior, written, written, stoodIn);
    }

    /** The key of one composed row, under the behavior whose block it belongs in. */
    public static RowKey of(String behavior, Generator.GeneratedRow row) {
        return new RowKey(behavior, row.inputs().stream().map(FixtureTemplate::text).toList(),
                row.inputs().stream().map(FixtureTemplate::meaning).toList(),
                row.answers().stream().map(RowKey::spelled).toList());
    }

    /** The same row when it puts in the same values, whatever they were written as. */
    @Override
    public boolean equals(Object other) {
        return other instanceof RowKey that && behavior.equals(that.behavior)
                && meant.equals(that.meant) && stoodIn.equals(that.stoodIn);
    }

    @Override
    public int hashCode() {
        return Objects.hash(behavior, meant, stoodIn);
    }

    /**
     * One answer a row states, as what tells it from another.
     *
     * <p>The dependency under the module that declares it, because two modules may declare
     * behaviors of one name and a key that left the module off would join two rows standing two
     * dependencies in.
     *
     * <p>A row leaning on the module's table writes no value at it, which is what the name standing
     * alone says. Spelt as though it wrote one, two rows a person pastes different text for would
     * come out as one piece of work.
     */
    private static String spelled(StoodInAnswer stood) {
        String named = stood.dependency().module() + "." + stood.dependency().name();
        return switch (stood) {
            case StoodInAnswer.OnTheRow(var _, var value) -> named + " = " + value.text();
            case StoodInAnswer.InTheModule _ -> named;
        };
    }

    /** The values as one line, which is how a row reads where it is written. */
    public String inputs() {
        return String.join(", ", written);
    }
}
