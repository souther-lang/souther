package souther.compiler.inputs;

import souther.compiler.types.Type;

import java.util.List;
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
 * that says the walk kept the order as well. The one run here that does is a total of what was
 * computed of each element by where it stands, and it holds that something
 * ({@link InTheOrderWritten}).
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
     * Whether the run is the elements of one container, one value for each: then how many it holds
     * is how many that container holds, and a count of it is a taking of the container's place.
     */
    default boolean isInOneContainer() {
        return switch (this) {
            case ProjectedOccurrences _, ComputedOccurrences _ -> true;
            case FlattenedOccurrences _, ReachableNodes _ -> false;
        };
    }

    /**
     * The same run, over the values read from where {@code moved} puts this one's — or null where
     * what stands there is no one run, as a run inside an element of another container is not.
     */
    default RunSource movedTo(UnaryOperator<TermPath> moved) {
        TermPath at = moved.apply(subjectPath());
        return switch (this) {
            case ProjectedOccurrences _ -> overTheOccurrencesAt(at);
            // Moved inside another container the run would be over some of the occurrences of the
            // path it was over every one of, so it keeps the containers it was in.
            case FlattenedOccurrences flat -> at != null
                    && at.containersHoldingIt().size() == flat.subjectPath().containersHoldingIt().size()
                    ? new FlattenedOccurrences(at) : null;
            // What was shown of the order was shown of the elements where they stood, and nothing
            // says those moved to stand in it, so a run that needs the order does not move.
            case ComputedOccurrences computed -> computed.order() != null ? null
                    : computedOverTheElementsAt(at, computed.computation(), computed.each(), null);
            // The nodes below a node are the same fields of it wherever it stands, and moved
            // inside a container it is one tree of many.
            case ReachableNodes nodes ->
                    overTheNodesBelow(at, nodes.through(), nodes.container());
        };
    }

    /**
     * Every node a tree holds from the node at {@code root} down through {@code through}, or the
     * elements of the container at {@code container} in each — or null where no one tree stands
     * there ({@link #oneTreeStandsAt}).
     */
    static RunSource overTheNodesBelow(TermPath root, List<String> through,
                                       List<String> container) {
        return root != null && oneTreeStandsAt(root)
                ? new ReachableNodes(root, through, container) : null;
    }

    /**
     * Whether the node at {@code root} is the root of one tree, which is what
     * {@link ReachableNodes} says of the path it holds.
     *
     * <p>Not where it stands inside a container. {@code trees[*]} says a tree of every element and
     * not which one: the nodes below every occurrence of it are every tree's, and a search down one
     * of them, read under a statement about each element, is over some of them. As
     * {@link #namesOneRun} is for the elements of one container, the path is the whole of what a
     * {@link ReachableNodes} holds, so it cannot tell those two apart.
     */
    static boolean oneTreeStandsAt(TermPath root) {
        return !root.insideAContainer();
    }

    /**
     * Every value standing at {@code where}, where the walk was shown to be over every occurrence
     * of it — or null where {@code where} is no position inside a container.
     *
     * <p>Asked of a position some reader certified, and not of any position ({@link
     * InputReads#everyElementOf}): a path inside more than one container is the path of every
     * list's elements in every element of the outer one, and a walk over one of those lists is over
     * some of them. {@link #overTheOccurrencesAt} stays the question about a position that is not
     * certified, and refuses what this accepts.
     */
    static RunSource overEveryOccurrenceAt(TermPath where) {
        if (where == null || !where.insideAContainer()) {
            return null;
        }
        return where.containersHoldingIt().size() == 1 ? new ProjectedOccurrences(where)
                : new FlattenedOccurrences(where);
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
     * The values standing at one position inside more than one container, every occurrence of it:
     * what each of the lists of an outer list holds, put end to end.
     *
     * <p>As many values as the position has in all, each of the walk's elements one of them. That
     * is the whole of what is claimed, and it is made only where the walk was shown to be over every
     * occurrence ({@link #overEveryOccurrenceAt}). The path alone says no such thing — a walk over
     * one element's list stands at the same path — so what makes this a run is where it was
     * made and not the path it holds, and a run made anywhere else would total some of the values
     * a rule is about the whole of.
     */
    record FlattenedOccurrences(TermPath subjectPath) implements RunSource {

        public FlattenedOccurrences {
            Objects.requireNonNull(subjectPath, "a run is read from somewhere");
            if (subjectPath.containersHoldingIt().size() < 2) {
                throw new IllegalArgumentException("`" + subjectPath + "` stands inside "
                        + subjectPath.containersHoldingIt().size()
                        + " containers, and a run over one is a ProjectedOccurrences");
            }
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
     * <p>A computation that turns on where an element stands claims the order as well, and holds
     * what showed it; one that does not claims nothing of the order and holds nothing. So two runs
     * of one such computation over one position are the same run whatever the walk that reached
     * them did to the order on the way.
     *
     * @param elements    where each element of the walked container stands
     * @param computation what the closure made of one of them
     * @param each        what one computed value stands as, with the names it is written under
     *                    taken off
     * @param order       that the walk was handed the elements in the order the row writes them,
     *                    where the computation reads where they stand; null where it does not
     */
    record ComputedOccurrences(TermPath elements, ElementValue computation, Type each,
                               InTheOrderWritten order) implements RunSource {

        public ComputedOccurrences {
            requireOneRun(elements);
            Objects.requireNonNull(computation, "a computed run is computed by something");
            Objects.requireNonNull(each, "and what it computes stands as some type");
            boolean byPosition = computation.readsThePosition();
            if (byPosition != (order != null)) {
                throw new IllegalArgumentException(byPosition
                        ? "{" + computation + "} turns on where each element stands, and nothing"
                                + " showed the walk was handed `" + elements + "` in the order"
                                + " written"
                        : "{" + computation + "} turns on no element's position, and claims"
                                + " nothing of their order");
            }
            if (order != null && !order.elements().equals(elements)) {
                throw new IllegalArgumentException("the order was shown of `" + order.elements()
                        + "` and not of `" + elements + "`");
            }
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
     * Every node a tree holds from the node at {@code root} down, each once: that node, and the
     * elements of the fields {@code through} of every node reached, which are nodes of the same
     * type — or, where {@code container} names fields of a node, the elements of the container
     * there in every one of those nodes.
     *
     * <p>A tree is finite however deep it goes, so these are as many values as it holds; and no
     * path names them, since the positions below a node of a type that holds itself are not read
     * again ({@link InputDomain}). Where the values are read from is the root, and the rest is
     * found by walking down from it.
     *
     * @param through   the fields of a node whose elements are the nodes below it, in one order
     * @param container the fields from a node to the container whose elements are the values, or
     *                  none where the values are the nodes
     */
    record ReachableNodes(TermPath root, List<String> through, List<String> container)
            implements RunSource {

        public ReachableNodes {
            Objects.requireNonNull(root, "a tree is walked from some node");
            through = List.copyOf(through);
            container = List.copyOf(container);
            if (through.isEmpty()) {
                throw new IllegalArgumentException("a tree goes below a node through something");
            }
            if (!oneTreeStandsAt(root)) {
                throw new IllegalArgumentException("`" + root + "` stands inside a container, and"
                        + " which of its trees a search went down is not said by it");
            }
        }

        @Override
        public TermPath subjectPath() {
            return root;
        }

        @Override
        public String toString() {
            return "{" + (container.isEmpty() ? "node" : String.join(".", container) + "[*]")
                    + " below " + root + " through " + through + "}";
        }
    }

    /**
     * That a walk was handed the elements at {@code elements}, every one of them once and in the
     * order the row writes them there.
     *
     * <p>Made where the reading of the input showed it ({@link InputReads#inTheOrderWrittenAt}),
     * and so in this package and nowhere else: a run is not made to claim the order by saying so.
     * Equal by the elements it was shown of, since that is all it says.
     */
    final class InTheOrderWritten {

        private final TermPath elements;

        InTheOrderWritten(TermPath elements) {
            this.elements = Objects.requireNonNull(elements, "an order is shown of some elements");
        }

        public TermPath elements() {
            return elements;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof InTheOrderWritten that && elements.equals(that.elements);
        }

        @Override
        public int hashCode() {
            return elements.hashCode();
        }

        @Override
        public String toString() {
            return "in the order " + elements + " is written";
        }
    }

    /**
     * The values computed of each element of the walk over {@code elements}, or null where those
     * elements are not one run — or where the computation turns on where each element stands and
     * {@code order} does not show the walk was handed them in the order written.
     *
     * @param order what showed the order, or null where nothing did
     */
    static RunSource computedOverTheElementsAt(TermPath elements, ElementValue computation,
                                               Type each, InTheOrderWritten order) {
        if (elements == null || computation == null || each == null || !namesOneRun(elements)) {
            return null;
        }
        if (!computation.readsThePosition()) {
            return new ComputedOccurrences(elements, computation, each, null);
        }
        return order != null && order.elements().equals(elements)
                ? new ComputedOccurrences(elements, computation, each, order) : null;
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
