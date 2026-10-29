package souther.compiler.inputs;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * The elements one comparison is read of, and which name stands for each.
 *
 * <p>A position inside a container's elements, {@code xs[*]}, says an element and not which one.
 * Two names that stand for two elements of one container are the same position, so a form that
 * holds both holds one number twice: {@code x - y} over two elements of {@code xs} is
 * {@code xs[*] - xs[*]}, which cancels to nothing and is read as a rule that cuts nothing, and
 * {@code x + y} is twice one number. Neither is what was written. A comparison is read of at most
 * one element of each container, and a name for another is one this refuses to take as a number of
 * the input rather than merge with the first.
 *
 * <p>An element is told from another by the container it is held in and the part of the entry it
 * is — the key or the value — and by nothing of its position. The elements of what a walk answered
 * are not those of what it was given, though a position may say so; and the key and the value of
 * one entry are two names for one element, which is what an entry is.
 *
 * <p>One of these for one comparison, shared by every number it names. Which element a name is of
 * is the environment's ({@link InputReads#elementsStoodForIn}); this holds what one comparison has
 * met of it. A reading of a number that stands alone, and names no other, has no comparison to be
 * held to and is asked with {@link #NONE}.
 */
public final class ElementsMet {

    /** Holds a reading to nothing: for a number read by itself. */
    public static final ElementsMet NONE = new ElementsMet(false);

    /** Which element of a container: the container and the part of the entry. */
    private record Slot(InputReads.ContainerOf container, HeldIn.Part part) {}

    /**
     * The names of elements that {@code sides} are written through, whatever else they name: which
     * entries a comparison is about, for a reader that has the comparison and not the reading of
     * it. Every one of them, two elements of one container among them: whether the comparison can
     * be read of both is what its reading says, and not which names it was written with.
     */
    public static Set<BindingId> namesOfElementsIn(List<Core> sides, InputReads at,
                                                  DeclarationNewtypes newtypes) {
        Set<BindingId> names = new LinkedHashSet<>();
        for (Core side : sides) {
            at.elementsStoodForIn(side, newtypes).forEach(stood -> names.add(stood.name()));
        }
        return Set.copyOf(names);
    }

    private final boolean holding;
    /** For each element of a container, the name that stands for it in this comparison. */
    private final Map<Slot, BindingId> standingFor = new LinkedHashMap<>();
    private boolean crowded;
    /** The elements asked of while a reading is being noted ({@link #noting}), shared by every
     *  copy made meanwhile; null when none is. */
    private Set<Slot> asked;

    /**
     * What a reading asked of the elements met and the names it left standing for them: the
     * elements it asked of, what stood for each when it began, and what stands for each when it
     * ended.
     *
     * <p>Another comparison whose elements stand as these did ({@link #agrees}) is asked the same
     * of each, in the same order, and answers the same; what it is left with is what this left
     * ({@link #takes}).
     */
    public static final class Footprint {

        private final boolean holding;
        private final Set<Slot> asked;
        private final Map<Slot, BindingId> began;
        private final Map<Slot, BindingId> ended;

        private Footprint(boolean holding, Set<Slot> asked, Map<Slot, BindingId> began,
                          Map<Slot, BindingId> ended) {
            this.holding = holding;
            this.asked = asked;
            this.began = began;
            this.ended = ended;
        }
    }

    /** A reading being noted, which says what it left once it has ended. */
    public static final class Noting {

        private final ElementsMet owner;
        private final ElementsMet began;
        private final Set<Slot> asked;
        private final Set<Slot> outer;

        private Noting(ElementsMet owner, ElementsMet began, Set<Slot> asked, Set<Slot> outer) {
            this.owner = owner;
            this.began = began;
            this.asked = asked;
            this.outer = outer;
        }

        /**
         * What the reading left of the elements, where it ended with {@code ended} met — or null
         * where a name was refused on the way, since that reading is not one to take from
         * another.
         */
        public Footprint ended(ElementsMet ended) {
            owner.asked = outer;
            if (ended != owner && ended.holding) {
                ended.asked = outer;
            }
            if (outer != null) {
                outer.addAll(asked);
            }
            if (!began.holding) {
                return new Footprint(false, Set.of(), Map.of(), Map.of());
            }
            if (ended.crowded || began.crowded) {
                return null;
            }
            Map<Slot, BindingId> from = new LinkedHashMap<>();
            Map<Slot, BindingId> to = new LinkedHashMap<>();
            for (Slot each : asked) {
                BindingId was = began.standingFor.get(each);
                if (was != null) {
                    from.put(each, was);
                }
                BindingId is = ended.standingFor.get(each);
                if (is != null) {
                    to.put(each, is);
                }
            }
            return new Footprint(true, Set.copyOf(asked), from, to);
        }
    }

    /** Begins noting which elements the reading that follows asks of, until {@link
     *  Noting#ended}. */
    public Noting noting() {
        Set<Slot> outer = asked;
        Set<Slot> mine = new LinkedHashSet<>();
        ElementsMet began = copied();
        if (holding) {
            asked = mine;
        }
        return new Noting(this, began, mine, outer);
    }

    /** Whether the elements stand here as they did when {@code footprint} began, in each that it
     *  asked of. */
    public boolean agrees(Footprint footprint) {
        if (holding != footprint.holding || crowded) {
            return false;
        }
        for (Slot each : footprint.asked) {
            if (!Objects.equals(standingFor.get(each), footprint.began.get(each))) {
                return false;
            }
        }
        return true;
    }

    /** Leaves the elements as {@code footprint} left them, which {@link #agrees}. */
    public void takes(Footprint footprint) {
        standingFor.putAll(footprint.ended);
    }

    /** A comparison's own, which nothing has been met of. */
    public ElementsMet() {
        this(true);
    }

    private ElementsMet(boolean holding) {
        this.holding = holding;
    }

    /**
     * Whether the number {@code node} names can be read beside what this comparison has met: it
     * can where every name in it that is an element of a container is the name that stands for
     * that element here, or the first to.
     */
    public boolean admits(Core node, InputReads at, DeclarationNewtypes newtypes) {
        if (!holding) {
            return true;
        }
        for (InputReads.ElementStood stood : at.elementsStoodForIn(node, newtypes)) {
            Slot slot = new Slot(stood.container(), stood.part());
            if (asked != null) {
                asked.add(slot);
            }
            BindingId had = standingFor.putIfAbsent(slot, stood.name());
            if (had != null && !had.equals(stood.name())) {
                crowded = true;
                return false;
            }
        }
        return true;
    }

    /**
     * What this comparison has met so far, held apart from it: a reading tried and not taken puts
     * this back, and leaves no name it met standing for an element.
     */
    public ElementsMet copied() {
        if (!holding) {
            return this;
        }
        ElementsMet copy = new ElementsMet(true);
        copy.standingFor.putAll(standingFor);
        copy.crowded = crowded;
        copy.asked = asked;
        return copy;
    }

    /**
     * Leaves the elements as {@code tried}, a copy of this a reading was tried on, left them:
     * the reading was taken, and this is shared by readers it cannot hand the copy to.
     */
    public void takes(ElementsMet tried) {
        if (!holding) {
            return;
        }
        standingFor.clear();
        standingFor.putAll(tried.standingFor);
        crowded = tried.crowded;
    }

    /** Whether a number was refused because it named another element of a container this
     *  comparison was already read of. */
    public boolean crowded() {
        return crowded;
    }
}
