package souther.compiler.observe;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;

/**
 * What one dependency was stated to answer while a row runs.
 *
 * <p>A row of a behavior that depends on something injected does not run against its inputs alone:
 * something answers that dependency while it runs, and what it answers is written down beside the
 * row. This is that, as something that did not read the source can hold it — an output whose
 * dependency is an import has an answer for the import rather than an implementation of it.
 *
 * <p>What was written and not what a run built from it. A run turns this into an instance of the
 * dependency's own base in the loader the implementation came from, which is a piece of the compile
 * that made it; the entries and the answers are values, and they cross.
 *
 * <p>One shape for the two ways of writing one. A {@code with dep = value} on the row answers the
 * same value whatever it is asked, and a {@code fake dep | table} beside the rows dispatches on what
 * it is asked; a {@code with} is a table that lists nothing and answers everything, so it is that
 * table here. Which of the two was written is a fact about the text and not about what the
 * dependency answers, and a reader told them apart would have two ways to ask one question.
 *
 * <p>Nothing here dispatches. What a table answers for arguments it does not list is the table's own
 * rule and not the reader's, and asking it takes what the declarations say a value's parts are — so
 * the asking is where a reading of the declarations is bound to it ({@code CheckedRow}), and what is
 * here is what the asking is made of.
 *
 * <p>A class and not a record, so that a stand-in holding a value that could not be carried cannot
 * be made. It is made by the reading that decides that ({@link RowStatements.StandInRead#of}) and
 * nowhere else, which is what lets a reader take every value in one as a value that is there.
 *
 * <p>A value all the same, and it says so itself: a row's statement rides inside a query's answer,
 * and what stops that query is whether the answer equals the one before it.
 */
public final class StoodIn {

    private final ValueName.Behavior dependency;
    private final SourcePos at;
    private final List<Type> takes;
    private final List<Entry> entries;
    private final Otherwise otherwise;

    private StoodIn(ValueName.Behavior dependency, SourcePos at, List<Type> takes,
                    List<Entry> entries, Otherwise otherwise) {
        this.dependency = dependency;
        this.at = at;
        this.takes = List.copyOf(takes);
        this.entries = List.copyOf(entries);
        this.otherwise = otherwise;
    }

    /** For the reading that decides whether a stand-in can be handed over, having decided it. */
    static StoodIn of(ValueName.Behavior dependency, SourcePos at, List<Type> takes,
                      List<Entry> entries, Otherwise otherwise) {
        return new StoodIn(dependency, at, takes, entries, otherwise);
    }

    /**
     * The behavior this stands in for, as the declaration it is.
     *
     * <p>The module is part of it: a behavior depends on what its own module declares and on what
     * another's does alike, and the name the module the row is written in happens to reach it by is
     * not what it is.
     */
    public ValueName.Behavior dependency() {
        return dependency;
    }

    /** Where what stands in is written: the {@code with} on the row, or the table beside the rows. */
    public SourcePos at() {
        return at;
    }

    /**
     * What the dependency declares it takes, in the order it takes them.
     *
     * <p>Here rather than looked up. What an entry's arguments were built and compared against is
     * this, read where the stand-in was read; asked again of whatever a reader can reach the
     * dependency's declaration through, it would be a second reading of one declaration — and a
     * dependency this program does not declare, which is one another compile handed over, could not
     * be asked at all.
     *
     * <p>What a comparison is made at as well as how many are made: whether an argument that is a
     * sequence is the same one in another order is what the type reading it says.
     */
    public List<Type> takes() {
        return takes;
    }

    /**
     * What it was written to answer, in the order the answering reads them.
     *
     * <p>The order is the rule's and not a listing's: the first entry stating what it is asked is
     * the one that answers, so entries in another order are a stand-in that answers differently.
     * Empty for a stand-in that lists nothing.
     *
     * <p>Every one of these is an entry the stand-in can answer with. An entry a table is written
     * with that its own rule can never reach is a fact about the source, said where the table is
     * written, and it is not here — a reader walking these is walking answers, and one that had to
     * work out which of them are reachable would be dispatching for itself.
     */
    public List<Entry> entries() {
        return entries;
    }

    /** What it answers when it is asked something no entry states. */
    public Otherwise otherwise() {
        return otherwise;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof StoodIn it && dependency.equals(it.dependency) && at.equals(it.at)
                && takes.equals(it.takes) && entries.equals(it.entries)
                && otherwise.equals(it.otherwise);
    }

    @Override
    public int hashCode() {
        return (((dependency.hashCode() * 31 + at.hashCode()) * 31 + takes.hashCode()) * 31
                + entries.hashCode()) * 31 + otherwise.hashCode();
    }

    @Override
    public String toString() {
        return dependency + " " + entries + " " + otherwise;
    }

    /**
     * One entry: the arguments it answers for, and the answer it states for them.
     *
     * <p>The arguments in the order the dependency takes them, and all of them — a dependency taking
     * two is answered for a pair and not for either half, which is the same rule the language states
     * for what a fake's row is written as.
     */
    public record Entry(List<ObservedValue> arguments, ObservedValue answer, SourcePos at) {

        public Entry {
            arguments = List.copyOf(arguments);
            if (answer == null || at == null) {
                throw new IllegalArgumentException("an entry answers what it states, and is written"
                        + " somewhere");
            }
        }
    }

    /**
     * What a stand-in answers where no entry states what it was asked.
     *
     * <p>Two arms, and which of them it is is what the source wrote: a table with a {@code _} row
     * answers that row, and one without answers nothing. Said as arms rather than as an answer that
     * may be absent, so that a reader cannot read "nothing is stated for this" as "nothing is the
     * answer".
     */
    public sealed interface Otherwise {

        /** It answers this, whatever it was asked. */
        record Answer(ObservedValue value, SourcePos at) implements Otherwise {

            public Answer {
                if (value == null || at == null) {
                    throw new IllegalArgumentException("an answer is a value, written somewhere");
                }
            }
        }

        /**
         * It states no answer for anything it does not list.
         *
         * <p>Not an error and not an answer. A run that asked such a stand-in something it does not
         * list is a run that cannot go on, which the language says where the fake is used; a reader
         * that reaches this has asked the dependency something the row never covered, which is a
         * fact about the reader's own run.
         */
        record NothingStated() implements Otherwise {}
    }
}
