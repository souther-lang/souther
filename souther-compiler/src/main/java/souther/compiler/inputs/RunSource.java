package souther.compiler.inputs;

import souther.compiler.types.Type;

import java.util.Objects;
import java.util.function.UnaryOperator;

/**
 * Where the values an operation walked came from, for a number taken over a run of them.
 *
 * <p>A model writes {@code List.sum(List.map(f, xs))} and means the numbers at a place inside
 * {@code xs} added up. There is no position holding that list — the walk that made it is gone from
 * the tree by the time anything measures, and the list never stood anywhere a row writes — so what
 * such a number is taken of is said as where its values came from rather than as a location.
 *
 * <p><b>What is claimed is the values and their number, and nothing about their order.</b> As many
 * values as stand at the place named, each of them one of them: that is what a sum needs, since a
 * total does not depend on which came first. An operation that does depend on it — a first, a
 * running total, anything read by index — is not entitled to rest on this, and would need something
 * that says the walk kept the order as well.
 *
 * <p>Beside {@link TermPath} and not a kind of one. A path says where a location is and says
 * nothing about how many values stand there, deliberately: a rule written about a location and a
 * row walked to it meet by being written the same way, and a multiplicity in the path would make
 * two spellings of one location. So how many values a number is taken of is said here, by the term
 * that takes it.
 */
public sealed interface RunSource {

    /** Where the values are read from. */
    TermPath subjectPath();

    /**
     * The same run, over the values read from where {@code moved} puts this one's — or null where
     * what stands there is no one run, as a run inside an element of another container is not.
     */
    default RunSource movedTo(UnaryOperator<TermPath> moved) {
        TermPath at = moved.apply(subjectPath());
        return switch (this) {
            case ProjectedOccurrences _ -> overTheOccurrencesAt(at);
            case ComputedOccurrences computed ->
                    computedOverTheElementsAt(at, computed.computation(), computed.each());
        };
    }

    /**
     * The values a walk over {@code where} was taken of, or null where what is read from there is
     * not one run.
     *
     * <p>The one place that decides it, so a reader asking for a run either gets one that means what
     * this promises or gets nothing. Asked as a question first and refused in the constructor after,
     * because a reader that has to catch a refusal is a reader that will one day not.
     */
    static RunSource overTheOccurrencesAt(TermPath where) {
        return where != null && namesOneRun(where) ? new ProjectedOccurrences(where) : null;
    }

    /**
     * Whether every occurrence of {@code where} is in one run, which is what
     * {@link ProjectedOccurrences} says of the path it holds.
     *
     * <p>One container, and the two ways of not being one are one question. None of them is a run at
     * all — a position holding one value is one value. Two of them is a run this cannot name:
     * {@code groups[*].lines[*].amount} says every line of every group, a walk over one group's
     * lines is over some of them, and the path is the whole of what a {@link ProjectedOccurrences}
     * holds, so it cannot tell those two apart. Asked as one question because it is one invariant,
     * and a reader who has a third thing to say about a path says it here rather than beside it.
     *
     * <p>What would lift the second is a run that names which occurrences it is over, and that is a
     * thing this representation does not have rather than a shape nothing writes. Refused until it
     * does, so the gap is one reading short and never a line drawn wrong.
     */
    private static boolean namesOneRun(TermPath where) {
        return where.containersHoldingIt().size() == 1;
    }

    /**
     * The values standing at one position, each element of the walk being one of them.
     *
     * <p>What has to be shown before one of these is made: as many values as the position has, and
     * each of the walk's elements the value at one of them. A construction that keeps some of what
     * it was given, or that answers one element for two, is not this — the numbers added up would
     * be a subset or a multiset of what the row holds, and a rule about the total would be measured
     * against something the model does not state.
     *
     * <p>And every occurrence of the path is in the run, which is what the path being the whole of
     * what this holds comes to. {@link #namesOneRun} is that, asked of every one of these however it
     * was reached.
     */
    record ProjectedOccurrences(TermPath subjectPath) implements RunSource {

        public ProjectedOccurrences {
            requireOneRun(subjectPath);
        }

        @Override
        public String toString() {
            return subjectPath.toString();
        }
    }

    /**
     * The values a walk computed of each element standing at one position.
     *
     * <p>As many values as there are elements, each made of that element by {@code computation}.
     * What is claimed is the same as of {@link ProjectedOccurrences} — one value per element, every
     * element in it — with the value no longer a place of the element but what the closure made of
     * it. The elements stand at {@code elements}; what is added up is not at any position, which is
     * why this is a source of its own and not a path with something written on it. A path says where
     * an input's values are, and a multiplicity or an operation in one would make two spellings of a
     * location.
     *
     * <p>Two runs over the same elements are two runs when they compute different things: the total
     * of {@code q * 2} is not the total of {@code q}, and what makes them different is the
     * computation, so it is part of what these are equal by.
     *
     * @param elements    where each element of the walked container stands
     * @param computation what the closure made of one of them
     * @param each        what one computed value stands as, with the names it is written under
     *                    taken off
     */
    record ComputedOccurrences(TermPath elements, ElementValue computation, Type each)
            implements RunSource {

        public ComputedOccurrences {
            requireOneRun(elements);
            Objects.requireNonNull(computation, "a computed run is computed by something");
            Objects.requireNonNull(each, "and what it computes stands as some type");
        }

        @Override
        public TermPath subjectPath() {
            return elements;
        }

        @Override
        public String toString() {
            return "{" + computation + " | " + elements + "}";
        }
    }

    /**
     * The values computed of each element of the walk over {@code elements}, or null where those
     * elements are not one run.
     */
    static RunSource computedOverTheElementsAt(TermPath elements, ElementValue computation,
                                               Type each) {
        return elements != null && computation != null && each != null && namesOneRun(elements)
                ? new ComputedOccurrences(elements, computation, each) : null;
    }

    /** The one invariant of every run, said as a refusal for a run made without asking. */
    private static void requireOneRun(TermPath where) {
        Objects.requireNonNull(where, "a run is read from somewhere");
        // One invariant, and the two ways of failing it are two sentences about it rather than
        // two guards: a reader with a third thing to say about the path says it in the question.
        if (!namesOneRun(where)) {
            throw new IllegalArgumentException(where.insideAContainer()
                    ? "a run is over every occurrence of the path it is read from, and `"
                            + where + "` stands inside "
                            + where.containersHoldingIt().size()
                            + " containers, so which of its occurrences a walk was over is not"
                            + " said by it"
                    : "a run stands inside a container, and `" + where + "` is one"
                            + " position holding one value");
        }
    }
}
