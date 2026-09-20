package souther.bench;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * What a copy that keeps no order hands its readers, and where a reader takes that order.
 *
 * <p>A value made by {@code Set.copyOf} or {@code Map.copyOf} iterates in an order the run decides.
 * Nothing wrong in holding one: two of them are equal whatever order they were built in, and asked
 * whether they hold a key or how many they hold, they answer the same in every run. What is wrong is
 * a reader that turns the iteration into an answer — a list of what was met, the first that
 * matched, a text that joins them — because that answer is then a function of the run.
 *
 * <p>So the question is not whether anything iterates. A reader may walk the whole of one to hand
 * it to something that puts it in an order, or to fold it with an operation that does not care
 * which comes first. The question is whether an iteration reaches an answer before either of those
 * has happened, and that is followed here, through locals, fields, arguments and returns, over the
 * compiled classes and not over their sources.
 *
 * <p>What a value can be, and only the last three are an answer. A {@link Kind#COLLECTION} is the
 * unordered value itself, or a view of it; a {@link Kind#TRAVERSAL} is an iterator or a stream over
 * one; a {@link Kind#SEQUENCE} is a container whose order came from a traversal — a list, an array,
 * a text; a {@link Kind#PICKED} is the element a walk is at; and a {@link Kind#CHOSEN} is the one a
 * call selected by where it stands. An answer that is stored, or that leaves a method nothing
 * reads, has become one the run decided.
 */
final class SaltedOrder {

    private SaltedOrder() {}

    /** What a value is, as far as its order goes. */
    enum Kind {

        /** A set, a map, or a view of one, whose iteration order is the run's. */
        COLLECTION,

        /** An iterator or a stream over one of those. */
        TRAVERSAL,

        /** A list, an array or a text put together in the order a traversal gave. */
        SEQUENCE,

        /**
         * One element, or one entry, a traversal is at. Every element of a walk is one of these in
         * turn, so what folds them all is not the order's business; one that is kept, returned or
         * stored is whichever the walk was at last.
         */
        PICKED,

        /** The one element a call selects by where it stands: the first, the last, the third. */
        CHOSEN,

        /** A collector that puts what it is given in the order it arrives in. */
        ORDERED_COLLECTOR,

        /** A collector that puts what it is given where an order plays no part. */
        UNORDERED_COLLECTOR,

        /** A function, named by the method that is its body, which is what a call on it runs. */
        FUNCTION
    }

    /**
     * One kind of one value, from one copy.
     *
     * @param origin the copy it began at, or for a {@link Kind#FUNCTION} the method that is its body
     * @param site   for an answer, the call that made the order an answer, which is where it is to
     *               be put right; empty for anything that is not one
     */
    record Tag(Kind kind, String origin, String site) {

        Tag(Kind kind, String origin) {
            this(kind, origin, "");
        }

        /** The same tag, made an answer at {@code where} unless it already was one somewhere. */
        Tag madeAt(String where) {
            return isAnAnswer() && site.isEmpty() ? new Tag(kind, origin, where) : this;
        }

        /** Whether an order the run decided is in this value already. */
        boolean isAnAnswer() {
            return kind == Kind.SEQUENCE || kind == Kind.CHOSEN;
        }

        /** Whether this is what a walk gave, an element or something made of the elements in turn. */
        boolean isPositional() {
            return isAnAnswer() || kind == Kind.PICKED;
        }

        /** Whether this is one of the kinds of thing that came out of a copy. */
        boolean cameOutOfACopy() {
            return kind == Kind.COLLECTION || kind == Kind.TRAVERSAL || isPositional();
        }
    }

    /**
     * A value the analysis holds on the stack or in a local.
     *
     * <p>{@code alloc} says which object made here it is, so that filling one through a call on it
     * is seen by every place the same object is held. {@code home} says where it was last read
     * from, a local or a field, which is how a call on a value taken out of a field is written back
     * to it. {@code made} is the class it was made from, since a call that only names an interface
     * cannot say whether {@code add} on it keeps an order.
     */
    record Val(Set<Tag> tags, boolean wide, int alloc, String made, String home) {

        static final Val CLEAN = new Val(Set.of(), false, -1, null, null);

        static final Val CLEAN_WIDE = new Val(Set.of(), true, -1, null, null);

        Val {
            // Held in the order they were put in, so that walking them says the same twice: a copy
            // made by Set.copyOf is the very thing this walk is about.
            tags = Collections.unmodifiableSet(new LinkedHashSet<>(tags));
        }

        static Val of(Set<Tag> tags) {
            return new Val(tags, false, -1, null, null);
        }

        static Val of(Tag... tags) {
            return of(Set.of(tags));
        }

        static Val clean(boolean wide) {
            return wide ? CLEAN_WIDE : CLEAN;
        }

        boolean isClean() {
            return tags.isEmpty();
        }

        Val withTags(Set<Tag> other) {
            return new Val(other, wide, alloc, made, home);
        }

        Val withHome(String at) {
            return new Val(tags, wide, alloc, made, at);
        }

        Val withMade(String type) {
            return new Val(tags, wide, alloc, type, home);
        }

        Val withAlloc(int id) {
            return new Val(tags, wide, id, made, home);
        }

        Val asWide(boolean isWide) {
            return new Val(tags, isWide, alloc, made, home);
        }

        Val plus(Collection<Tag> more) {
            if (tags.containsAll(more)) {
                return this;
            }
            Set<Tag> all = new LinkedHashSet<>(tags);
            all.addAll(more);
            return withTags(all);
        }

        /** What a place holds when two ways of reaching it meet. */
        Val join(Val other) {
            if (equals(other)) {
                return this;
            }
            Set<Tag> all = new LinkedHashSet<>(tags);
            all.addAll(other.tags);
            return new Val(all, wide || other.wide, alloc == other.alloc ? alloc : -1,
                    made != null && made.equals(other.made) ? made : null,
                    home != null && home.equals(other.home) ? home : null);
        }

        /** The copies any of what is here came out of. */
        Set<String> origins() {
            Set<String> out = new TreeSet<>();
            for (Tag each : tags) {
                if (each.cameOutOfACopy()) {
                    out.add(each.origin());
                }
            }
            return out;
        }

        boolean has(Kind kind) {
            for (Tag each : tags) {
                if (each.kind() == kind) {
                    return true;
                }
            }
            return false;
        }

        boolean cameOutOfACopy() {
            for (Tag each : tags) {
                if (each.cameOutOfACopy()) {
                    return true;
                }
            }
            return false;
        }

        boolean holdsAnAnswer() {
            for (Tag each : tags) {
                if (each.isAnAnswer()) {
                    return true;
                }
            }
            return false;
        }

        /** The same, once the walk the elements were of has ended. */
        Val withoutElements() {
            if (!has(Kind.PICKED)) {
                return this;
            }
            Set<Tag> kept = new LinkedHashSet<>();
            for (Tag each : tags) {
                if (each.kind() != Kind.PICKED) {
                    kept.add(each);
                }
            }
            return withTags(kept);
        }

        /**
         * What here is a plurality that came out of a copy, as against an element of one. An element
         * that is itself a collection has an order of its own to be read in, which is not this
         * one's.
         */
        Val collections() {
            Set<Tag> out = new LinkedHashSet<>();
            for (Tag each : tags) {
                if (each.kind() == Kind.COLLECTION || each.kind() == Kind.TRAVERSAL
                        || each.kind() == Kind.SEQUENCE) {
                    out.add(each);
                }
            }
            return Val.of(out);
        }

        /** The same origins as one kind. */
        Set<Tag> as(Kind kind) {
            Set<Tag> out = new LinkedHashSet<>();
            for (String origin : origins()) {
                out.add(new Tag(kind, origin));
            }
            return out;
        }

        /** The functions here, which are what a call on this runs. */
        Set<Tag> functions() {
            Set<Tag> out = new LinkedHashSet<>();
            for (Tag each : tags) {
                if (each.kind() == Kind.FUNCTION) {
                    out.add(each);
                }
            }
            return out;
        }
    }

    /**
     * A reader that took an order into an answer.
     *
     * @param reader the method that did, with the class it is in
     * @param what   the step that made it an answer, in words
     * @param origins the copies the order came out of
     */
    record Finding(String reader, String what, Set<String> origins) {}

    /**
     * What the whole reading came to.
     *
     * @param roots   every copy the reading began at
     * @param findings every place an order became an answer
     * @param reached for each copy, where what came out of it went in the end: to a crossing that
     *                puts it in an order, or into a value that holds it and is asked, in turn
     */
    record Reading(Set<String> roots, List<Finding> findings, Map<String, Set<String>> reached) {

        Reading {
            roots = Collections.unmodifiableSet(new LinkedHashSet<>(roots));
            findings = List.copyOf(findings);
            reached = Collections.unmodifiableMap(new LinkedHashMap<>(reached));
        }

        /** Every finding, one to a line, so that a failure says what to read. */
        List<String> described() {
            List<String> out = new ArrayList<>();
            for (Finding each : findings) {
                out.add(each.reader() + " — " + each.what() + " (from " + each.origins() + ")");
            }
            out.sort(Comparator.naturalOrder());
            return out;
        }

        /** The reached-sets in a fixed order, which is the only form a report of them is read in. */
        Map<String, Set<String>> reachedInOrder() {
            Map<String, Set<String>> out = new TreeMap<>();
            for (Map.Entry<String, Set<String>> each : reached.entrySet()) {
                out.put(each.getKey(), new TreeSet<>(each.getValue()));
            }
            return out;
        }
    }
}
