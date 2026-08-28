package souther.compiler.check;

import souther.compiler.types.BindingId;

import java.util.EnumMap;
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
 * <p>Three facts and not one, because they license different things. Where an operation answers
 * the elements it was given — a {@code filter}, a {@code distinct} — the two bindings hold the same
 * values, so a rule about one is a rule about the other and a reading may walk through. Where it
 * answers what a closure made of them, the values came from there and are not those values: what a
 * rule about them means for the position they came from is not settled by knowing where they came
 * from, and a reading that walked through would put a line at a position whose values are not the
 * ones the rule is about.
 *
 * <p>And where the operation answers exactly one of those per element, the closure's own parameter
 * is named beside the container it walks. That is a stronger statement than where the values came
 * from and a narrower one: it says the answers and the elements correspond, which is what a number
 * over the whole run needs and what a walk keeping some of what it was given does not have.
 * {@link #projectedFrom} is that, and the operation it was proved of is gone by the time anything
 * reads the tree — so it is proved where the operation stands and carried by binding.
 *
 * <p><b>Asked one fact at a time, and never as a table.</b> The three are kept in one place because
 * they obey one law where a body is copied ({@link CopyableFactKind}), and that is a reason for the
 * shape inside and for nothing outside: a reader wants to know what one binding's elements came
 * from, and the question it asks is that. Nothing here hands out the table, so no reader can come to
 * depend on this being a table — which is what would make a fact obeying a different law hard to add
 * beside these, exactly the thing the kinds were named narrowly to keep possible.
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
     * <p>Named for what the facts have in common rather than for their being relations between
     * bindings. A fact from one binding to several, or one a copy moves only one end of, obeys
     * nothing said here and does not belong among these however much it reads like one — put here,
     * it would be carried by a law it does not keep.
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
    public static final ElementProvenance NONE = new ElementProvenance(Map.of());

    private final Map<CopyableFactKind, Map<BindingId, BindingId>> byKind;

    /** Every kind is present, so a reader of one never meets an absence standing for an empty
     *  table, and the tables are this value's rather than any caller's. */
    private ElementProvenance(Map<CopyableFactKind, Map<BindingId, BindingId>> facts) {
        Map<CopyableFactKind, Map<BindingId, BindingId>> held =
                new EnumMap<>(CopyableFactKind.class);
        for (CopyableFactKind kind : CopyableFactKind.values()) {
            held.put(kind, Map.copyOf(facts.getOrDefault(kind, Map.of())));
        }
        this.byKind = Map.copyOf(held);
    }

    /** What one kind of fact this holds, as the bindings it is said of against the bindings it says
     *  them of. Here for what is written beside it and for what holds the law; a reader asks about
     *  one binding. */
    Map<BindingId, BindingId> of(CopyableFactKind kind) {
        return byKind.get(kind);
    }

    /** Every closure parameter of a one-per-element walk, against the container walked. The one
     *  kind a reader beside this asks about as a whole, to say how many such walks a body has. */
    Map<BindingId, BindingId> projectedFrom() {
        return of(CopyableFactKind.PROJECTS_EACH_ELEMENT_OF);
    }

    /** The binding whose elements {@code binding} holds too, or null where none does. */
    public BindingId sameElementsAs(BindingId binding) {
        return binding == null ? null : of(CopyableFactKind.HOLDS_THE_SAME_AS).get(binding);
    }

    /** The binding whose elements {@code binding}'s were made from, or null where none was. */
    public BindingId madeFrom(BindingId binding) {
        return binding == null ? null : of(CopyableFactKind.DERIVES_FROM).get(binding);
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
        return parameter == null ? null
                : of(CopyableFactKind.PROJECTS_EACH_ELEMENT_OF).get(parameter);
    }

    public boolean isEmpty() {
        return byKind.values().stream().allMatch(Map::isEmpty);
    }

    @Override
    public boolean equals(Object other) {
        return this == other
                || other instanceof ElementProvenance that && byKind.equals(that.byKind);
    }

    @Override
    public int hashCode() {
        return byKind.hashCode();
    }

    @Override
    public String toString() {
        return "ElementProvenance" + byKind;
    }

    /** What an expansion writes down as it goes. */
    static final class Builder {

        private final Map<CopyableFactKind, Map<BindingId, BindingId>> byKind =
                new EnumMap<>(CopyableFactKind.class);

        Builder() {
            for (CopyableFactKind kind : CopyableFactKind.values()) {
                byKind.put(kind, new LinkedHashMap<>());
            }
        }

        void holdsTheSameAs(BindingId binding, BindingId container) {
            byKind.get(CopyableFactKind.HOLDS_THE_SAME_AS).putIfAbsent(binding, container);
        }

        void derivesFrom(BindingId binding, BindingId container) {
            byKind.get(CopyableFactKind.DERIVES_FROM).putIfAbsent(binding, container);
        }

        /** {@code parameter} is the closure parameter of a walk answering one per element of
         *  {@code container}. */
        void projectsEachElementOf(BindingId parameter, BindingId container) {
            byKind.get(CopyableFactKind.PROJECTS_EACH_ELEMENT_OF).putIfAbsent(parameter, container);
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
         * before it. Asked once against both, because it is one thing that must not happen and a
         * question asked of the table alone would let a renaming carrying two names for one binding
         * through.
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
            for (Map<BindingId, BindingId> facts : byKind.values()) {
                Map<BindingId, BindingId> induced = new LinkedHashMap<>();
                renaming.forEach((of, here) -> {
                    BindingId from = facts.get(of);
                    BindingId there = from == null ? null : renaming.get(from);
                    if (there == null) {
                        return;
                    }
                    BindingId already =
                            induced.containsKey(here) ? induced.get(here) : facts.get(here);
                    if (already != null) {
                        throw new IllegalStateException(
                                "two facts landed on one binding: " + here + " was said of "
                                        + already + " before this copy said " + there);
                    }
                    induced.put(here, there);
                });
                facts.putAll(induced);
            }
        }

        ElementProvenance built() {
            ElementProvenance built = new ElementProvenance(byKind);
            return built.isEmpty() ? NONE : built;
        }
    }
}
