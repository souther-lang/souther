package souther.compiler.program;

import souther.compiler.diag.SourcePos;
import souther.compiler.observe.Comparisons;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.Position;
import souther.compiler.observe.StoodIn;
import souther.compiler.observe.ValueTypes;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * What answers one of a behavior's dependencies while a row of it runs, for an output outside this
 * compiler.
 *
 * <p>A row of a behavior that depends on something injected does not run against its inputs alone.
 * An output emits that dependency as an import, and what it has to put behind the import is an
 * answer rather than an implementation: this is what the row states that answer to be, and asking
 * it is asking what the row was written to run against.
 *
 * <p>What it answers is asked here rather than read off {@link #stated}. Which entry answers is the
 * table's own rule — the first stating what it was asked, and otherwise whatever it was written to
 * answer for the rest — and whether an argument is what an entry states is the language's, since
 * two values differ when their types differ as much as when their contents do. A reader deciding
 * either for itself would have the fake answer one thing in this compile and another in the output
 * built from it, which is the row running against something nobody wrote.
 *
 * <p>What it takes is what {@link CheckedRow.SelfContained#holds} takes: values as they were
 * observed. An output that can say what its own answer was — which holding a row to what it states
 * already asks of it — can say what its emission handed the import.
 */
public final class StandsIn {

    private final StoodIn stated;
    private final ValueTypes types;
    private final List<Position> arguments;

    StandsIn(StoodIn stated, ValueTypes types) {
        if (stated == null || types == null) {
            throw new IllegalArgumentException("what stands in for a dependency is what the row"
                    + " states of it, read with what the declarations say");
        }
        this.stated = stated;
        this.types = types;
        List<Position> arguments = new ArrayList<>();
        // Where each of the dependency's arguments stands, off what the stand-in states the
        // dependency takes. Read off the declaration a second time — through whatever this program
        // publishes for that behavior — it could be a reading the entries were never built against,
        // and a dependency declared in a module this compile only read would have none here at all.
        for (Type takes : stated.takes()) {
            arguments.add(Position.at(takes));
        }
        this.arguments = List.copyOf(arguments);
    }

    /** The behavior this stands in for, which is the one an output emits as an import. */
    public ValueName.Behavior dependency() {
        return stated.dependency();
    }

    /**
     * What the row states it answers.
     *
     * <p>What a report shows and what a generated test is written from. Not how to answer: the
     * entries are in the order the rule reads them, and the rule is {@link #answering}.
     */
    public StoodIn stated() {
        return stated;
    }

    /**
     * What it answers for {@code arguments}, in the order the dependency takes them.
     *
     * <p>The stand-in's own rule and not a lookup a reader arranges: the first entry stating these
     * arguments answers, and where none states them the answer is whatever the stand-in was written
     * to answer for the rest — which may be nothing.
     */
    public Answer answering(List<ObservedValue> asked) {
        if (asked == null) {
            throw new IllegalArgumentException("a stand-in is asked what it answers for values");
        }
        for (ObservedValue value : asked) {
            if (value == null) {
                throw new IllegalArgumentException("a stand-in is asked what it answers for"
                        + " values");
            }
        }
        if (asked.size() != arguments.size()) {
            // A call and not a value of one: what a dependency taking two is asked is a pair, and
            // an entry stating a pair states neither half of it on its own.
            throw new IllegalArgumentException("`" + dependency().name() + "` takes "
                    + arguments.size() + " and was asked what it answers for " + asked.size());
        }
        for (StoodIn.Entry entry : stated.entries()) {
            if (states(entry.arguments(), asked)) {
                return new Answer.TheValue(entry.answer());
            }
        }
        return switch (stated.otherwise()) {
            case StoodIn.Otherwise.Answer(ObservedValue value, SourcePos _) ->
                    new Answer.TheValue(value);
            case StoodIn.Otherwise.NothingStated _ -> new Answer.NothingStated();
        };
    }

    /**
     * Whether an entry states the arguments a call arrived with.
     *
     * <p>Each of them at the place the dependency's declaration puts it, which is what says whether
     * a sequence there is compared in order. A dependency taking several is answered for all of
     * them together: an entry states a call and not one argument of one.
     */
    private boolean states(List<ObservedValue> entry, List<ObservedValue> asked) {
        if (entry.size() != asked.size()) {
            return false;
        }
        for (int i = 0; i < entry.size(); i++) {
            if (!Comparisons.same(entry.get(i), asked.get(i), types, arguments.get(i))) {
                return false;
            }
        }
        return true;
    }

    @Override
    public String toString() {
        return stated.toString();
    }

    /**
     * What a stand-in answers for one call.
     *
     * <p>Two arms rather than a value that may be absent. A stand-in that states nothing for what it
     * was asked has not answered with nothing — a run reaching that is a run the row never covered,
     * and a reader handed an absent value would put it behind the import as an answer.
     */
    public sealed interface Answer {

        /** It answers this. */
        record TheValue(ObservedValue value) implements Answer {

            public TheValue {
                if (value == null) {
                    throw new IllegalArgumentException("an answer is a value");
                }
            }
        }

        /** It states no answer for what it was asked. */
        record NothingStated() implements Answer {}
    }
}
