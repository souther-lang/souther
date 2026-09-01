package souther.compiler.check;

import souther.compiler.inputs.ElementQuestion;
import souther.compiler.types.BindingId;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Where the elements of what a binding holds came from, for the bindings an expansion wrote.
 *
 * <p>Written where the operation that says so is removed. A collection operation the library
 * declares as a body is spliced into whatever calls it, and afterwards the tree holds a walk with no
 * name on it — so what its answer held the elements of is a fact only the expansion had, and
 * recognising it again from the walk would read the shape a splice happens to leave.
 *
 * <p>Two kinds of fact, because they are about different things. One binding's elements stand to
 * another's as the same values or as values made from them ({@link ElementEdge}), and that is one
 * edge per binding. Beside it and not among them, a walk answering exactly one value per element
 * names its closure's own parameter against the container walked: that is a stronger statement and a
 * narrower one — it says the answers and the elements correspond, which is what a number over the
 * whole run needs and what a walk keeping some of what it was given does not have.
 * {@link #projectedFrom} is that, and the operation it was proved of is gone by the time anything
 * reads the tree, so it too is proved where the operation stands and carried by binding.
 *
 * <p><b>An edge is never handed out.</b> What one licenses is not a property of the edge but of the
 * question being asked, and a reader holding one could answer that for itself — beside the one place
 * that answers it, and free to differ. So the only way to read an edge is to name a question, and
 * {@link #predecessorOf} is the whole of what comes back.
 *
 * <p>Bindings and not expressions. A binding tells one occurrence from another, which is what two
 * calls of one operation need, where an expression does not survive being copied, renamed or
 * rewritten. What a binding survives is two different things, and they are not both free:
 *
 * <p><b>A rewrite keeps the binding.</b> A fold that only grows a collection becomes a walk over a
 * builder, and two such walks in a row become one; none of it mints a binding or renames one, so a
 * fact keyed this way is as true after it as before and nothing has to be done.
 *
 * <p><b>A copy makes new bindings, and the facts are carried across it.</b> Splicing a body in gives
 * every binding the body introduces one of the copy's own, so a fact left keyed on the original is
 * about bindings the copied tree does not have. The copy holds the whole renaming at the one moment
 * it is made, and {@link CopyableFactKind} is the law that says what to do with it there.
 *
 * <p>A value, compared by what it holds. It is part of an answer the query database keeps, and an
 * identity that differed between two readings of one source would make every edit look like a change
 * to everything downstream ({@link BindingId}).
 */
public final class ElementProvenance {

    /**
     * A kind of fact this holds, and the law every one of them obeys where a body is copied.
     *
     * <p>Each is one binding said of another, both written by an expansion, and the two are moved
     * together or not at all. So where a copy gives a body's bindings new ones under a renaming
     * {@code m}, the copy has the same fact of the bindings it made: {@code a R b} with both ends in
     * {@code m} induces {@code m(a) R m(b)}.
     *
     * <p>Named for what the facts have in common rather than for how they are held. Two of them are
     * one binding's edge to another and are kept as one edge; the third is kept beside it. What puts
     * all three here is that a copy carries them alike, and a fact from one binding to several, or
     * one a copy moves only one end of, obeys nothing said here and does not belong among these
     * however much it reads like one — put here, it would be carried by a law it does not keep.
     */
    enum CopyableFactKind {
        /** The two bindings hold the same values. */
        HOLDS_THE_SAME_AS,
        /** The first binding's elements were made from the second's. */
        DERIVES_FROM,
        /** The first binding is the closure parameter of a walk answering one per element of the
         *  second. */
        PROJECTS_EACH_ELEMENT_OF
    }

    /** Nothing was expanded, which is what a body calling no such operation comes to. */
    public static final ElementProvenance NONE =
            new ElementProvenance(Map.of(), Map.of());

    private final Map<BindingId, ElementEdge> edges;
    private final Map<BindingId, BindingId> projections;

    private ElementProvenance(Map<BindingId, ElementEdge> edges,
                              Map<BindingId, BindingId> projections) {
        this.edges = Map.copyOf(edges);
        this.projections = Map.copyOf(projections);
    }

    /**
     * The binding a walk asking {@code question} may go on to from {@code binding}, or null where
     * this question is not entitled to one and where nothing was recorded.
     *
     * <p>The one place an edge is read. Answered per question and never by asking whether this is
     * one of them: a question added here is one nobody has said what the edges mean for, and read as
     * "not that one" it would follow whichever edges the last question happened to leave — the
     * answer arrived at by not being asked.
     */
    public BindingId predecessorOf(BindingId binding, ElementQuestion question) {
        return switch (binding == null ? null : edges.get(binding)) {
            case null -> null;
            // The two bindings hold the same values, so either question goes on through.
            case ElementEdge.TheSameAs(var container) -> container;
            // What is made from a position came from it and is not it, so the walk after which
            // position an expression names stops where the elements stop being the same ones.
            case ElementEdge.MadeFrom(var container) -> switch (question) {
                case NAMED_POSITION -> null;
                case VALUE_ORIGIN -> container;
            };
        };
    }

    /**
     * What one kind of fact this holds, as the bindings it is said of against the bindings it says
     * them of. Here for what holds the law; a reader asks about one binding.
     */
    Map<BindingId, BindingId> of(CopyableFactKind kind) {
        if (kind == CopyableFactKind.PROJECTS_EACH_ELEMENT_OF) {
            return projections;
        }
        Map<BindingId, BindingId> out = new LinkedHashMap<>();
        edges.forEach((binding, edge) -> {
            if (kindOf(edge) == kind) {
                out.put(binding, edge.container());
            }
        });
        return Map.copyOf(out);
    }

    /** Which kind an edge is, said once so that an edge added is a kind the law has to place. */
    private static CopyableFactKind kindOf(ElementEdge edge) {
        return switch (edge) {
            case ElementEdge.TheSameAs _ -> CopyableFactKind.HOLDS_THE_SAME_AS;
            case ElementEdge.MadeFrom _ -> CopyableFactKind.DERIVES_FROM;
        };
    }

    /** Every closure parameter of a one-per-element walk, against the container walked. The one
     *  kind a reader beside this asks about as a whole, to say how many such walks a body has. */
    Map<BindingId, BindingId> projectedFrom() {
        return projections;
    }

    /**
     * The container {@code parameter} is the closure parameter of a one-per-element walk over, or
     * null where it is no such parameter.
     *
     * <p>What this licenses is one answer per element of that container, and nothing about the
     * order. A reader that has it still has to show what the answer is — where it stands in the
     * element it was made from — and that is a question about the expression the closure was, not
     * about this.
     */
    public BindingId projectedFrom(BindingId parameter) {
        return parameter == null ? null : projections.get(parameter);
    }

    public boolean isEmpty() {
        return edges.isEmpty() && projections.isEmpty();
    }

    @Override
    public boolean equals(Object other) {
        return this == other
                || other instanceof ElementProvenance that && edges.equals(that.edges)
                        && projections.equals(that.projections);
    }

    @Override
    public int hashCode() {
        return edges.hashCode() * 31 + projections.hashCode();
    }

    @Override
    public String toString() {
        return "ElementProvenance[edges=" + edges + ", projections=" + projections + "]";
    }

    /** What an expansion writes down as it goes. */
    static final class Builder {

        private final Map<BindingId, ElementEdge> edges = new LinkedHashMap<>();
        private final Map<BindingId, BindingId> projections = new LinkedHashMap<>();

        void holdsTheSameAs(BindingId binding, BindingId container) {
            putEdge(binding, new ElementEdge.TheSameAs(container));
        }

        void derivesFrom(BindingId binding, BindingId container) {
            putEdge(binding, new ElementEdge.MadeFrom(container));
        }

        /** {@code parameter} is the closure parameter of a walk answering one per element of
         *  {@code container}. */
        void projectsEachElementOf(BindingId parameter, BindingId container) {
            projections.putIfAbsent(parameter, container);
        }

        /**
         * The one place an edge is written, which is what makes a binding have at most one.
         *
         * <p>Writing the same edge again is the same fact and changes nothing. A different one is a
         * binding whose elements are said to be two things at once, and there is no reading of that
         * — kept, one of the two would be dropped by whichever arrived second, and a walk would go
         * on through an edge nobody wrote.
         */
        private void putEdge(BindingId binding, ElementEdge edge) {
            ElementEdge already = edges.putIfAbsent(binding, edge);
            if (already != null && !already.equals(edge)) {
                throw new IllegalStateException("the elements of " + binding + " are " + already
                        + " and " + edge);
            }
        }

        /**
         * Every fact said again of the bindings a copy made, under the renaming that copy is.
         *
         * <p>Induced and not moved. The body a copy was taken from is a body too — a lambda applied
         * at two places is copied twice, and what was proved of the original is still what it was —
         * so what this writes is a second fact beside the first rather than in place of it.
         *
         * <p>Both ends or neither, which is {@link CopyableFactKind}'s law. A fact one end of which
         * this renaming does not move is not this copy's fact, and half of it renamed would say of
         * one body's binding what was proved about another's.
         *
         * <p>The renaming and not whatever holds it. What is obeyed here is a law about facts and a
         * map from bindings to bindings, and nothing about how the map came to exist — so this is
         * held to on its own, by the map alone, rather than through the pass that copies bodies.
         *
         * <p><b>No two facts of one kind land on one binding.</b> A binding a copy minted is one
         * nothing has said anything of, so meeting one already answered is not a fact arriving twice
         * — it is two bindings given one name, whether the other came from this copy or from a copy
         * before it. Which is stricter than what an edge is written under: there, the same fact
         * twice is the same fact, and here the binding was to have been new.
         *
         * <p>Asked once against both, because it is one thing that must not happen and a question
         * asked of the table alone would let a renaming carrying two names for one binding through.
         *
         * <p>Refused where it would be written and not by walking the whole renaming, which would
         * be a claim about renamings this does not need and does not make: what must not happen is
         * two facts on one binding, and a renaming naming one binding twice with no fact on either
         * writes nothing here.
         *
         * <p>Walked from the renaming rather than from the table, so what this costs is the size of
         * the copy and not the size of what has been proved so far. Read the other way round, a body
         * with many walks in it would have every one of them looked at again at every copy, which is
         * a second reading of the whole table for work that is about one copy's bindings.
         *
         * <p>Gathered before any of it is written, since what is read is the table being added to.
         */
        void carriedAcross(Map<BindingId, BindingId> renaming) {
            if (renaming.isEmpty()) {
                return;
            }
            Map<BindingId, ElementEdge> inducedEdges = new LinkedHashMap<>();
            Map<BindingId, BindingId> inducedProjections = new LinkedHashMap<>();
            renaming.forEach((of, here) -> {
                ElementEdge edge = edges.get(of);
                BindingId movedEnd = edge == null ? null : renaming.get(edge.container());
                if (movedEnd != null) {
                    refuseSecond(here, inducedEdges.containsKey(here)
                            ? inducedEdges.get(here) : edges.get(here));
                    // An edge added is one this has to say how a copy carries, which is with the
                    // kind it was: the two ends move and what stands between them does not.
                    inducedEdges.put(here, switch (edge) {
                        case ElementEdge.TheSameAs _ -> new ElementEdge.TheSameAs(movedEnd);
                        case ElementEdge.MadeFrom _ -> new ElementEdge.MadeFrom(movedEnd);
                    });
                }
                BindingId walked = projections.get(of);
                BindingId movedWalked = walked == null ? null : renaming.get(walked);
                if (movedWalked != null) {
                    refuseSecond(here, inducedProjections.containsKey(here)
                            ? inducedProjections.get(here) : projections.get(here));
                    inducedProjections.put(here, movedWalked);
                }
            });
            inducedEdges.forEach(this::putEdge);
            projections.putAll(inducedProjections);
        }

        private static void refuseSecond(BindingId here, Object already) {
            if (already != null) {
                throw new IllegalStateException("two facts landed on one binding: " + here
                        + " was said of " + already + " before this copy said another");
            }
        }

        ElementProvenance built() {
            ElementProvenance built = new ElementProvenance(edges, projections);
            return built.isEmpty() ? NONE : built;
        }
    }
}
