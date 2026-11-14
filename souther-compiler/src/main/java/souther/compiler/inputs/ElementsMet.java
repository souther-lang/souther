package souther.compiler.inputs;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.core.Core;
import souther.compiler.inputs.ElementsNamed.Slot;
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
 * the input rather than merge with the first. Nor does it take a number read through a name whose
 * element is not known ({@link ElementsNamed#unnamed}): which element that is, is no more said than
 * which of two it is.
 *
 * <p>An element is told from another by the container it is held in and the part of the entry it
 * is — the key or the value. The container is the one the element stands in where it stands at a
 * position, which is where what an operation hands on of a container's elements stands, and what a
 * walk made otherwise; and the key and the value of one entry are two names for one element, which
 * is what an entry is.
 *
 * <p>One of these for one comparison, shared by every number it names. Which element a name is of
 * is the environment's ({@link InputReads#elementsNamedIn}); this holds what one comparison has
 * met of it. A reading of a number that stands alone, and names no other, has no comparison to be
 * held to and is asked with {@link #NONE}.
 */
public final class ElementsMet {

    /** Holds a reading to nothing: for a number read by itself. */
    public static final ElementsMet NONE = new ElementsMet(false);

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
            at.elementsNamedIn(side, newtypes).named().values().forEach(names::addAll);
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

    /**
     * What has been met, as it stood when it was taken ({@link #mark}): the names standing for the
     * elements, and whether a number was refused. It is a value and nothing puts anything in it, so
     * what is rewound to it is what it was taken as however often it is rewound to.
     */
    public static final class Mark {

        private final Map<Slot, BindingId> standingFor;
        private final boolean crowded;

        private Mark(Map<Slot, BindingId> standingFor, boolean crowded) {
            this.standingFor = standingFor;
            this.crowded = crowded;
        }
    }

    /** What has been met, to be put back by {@link #rewind}. */
    public Mark mark() {
        return new Mark(holding ? new LinkedHashMap<>(standingFor) : Map.of(), crowded);
    }

    /**
     * Puts what has been met back as it was at {@code mark}, in this and not in another: whoever
     * holds this holds what is put back, and a reading made on it before still reads what is.
     * Where a reading is not to be taken, it is rewound to what it began with; where its ways are
     * alternatives, each begins from the mark of the place they part at.
     */
    public void rewind(Mark mark) {
        if (!holding) {
            return;
        }
        standingFor.clear();
        standingFor.putAll(mark.standingFor);
        crowded = mark.crowded;
    }

    /** A reading being noted, which says what it left once it has ended. */
    public static final class Noting {

        private final ElementsMet owner;
        private final Mark began;
        private final Set<Slot> asked;
        private final Set<Slot> outer;

        private Noting(ElementsMet owner, Mark began, Set<Slot> asked, Set<Slot> outer) {
            this.owner = owner;
            this.began = began;
            this.asked = asked;
            this.outer = outer;
        }

        /**
         * What the reading left of the elements — or null where a name was refused on the way,
         * since that reading is not one to take from another.
         */
        public Footprint ended() {
            owner.asked = outer;
            if (outer != null) {
                outer.addAll(asked);
            }
            if (!owner.holding) {
                return new Footprint(false, Set.of(), Map.of(), Map.of());
            }
            if (owner.crowded || began.crowded) {
                return null;
            }
            Map<Slot, BindingId> from = new LinkedHashMap<>();
            Map<Slot, BindingId> to = new LinkedHashMap<>();
            for (Slot each : asked) {
                BindingId was = began.standingFor.get(each);
                if (was != null) {
                    from.put(each, was);
                }
                BindingId is = owner.standingFor.get(each);
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
        Mark began = mark();
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

    /**
     * Leaves the elements as {@code footprint} left them, which {@link #agrees}, and counts the
     * elements it asked of among those the reading being noted asks of, as reading it again would
     * have: a reading that is taken from another is asked of the same elements by whoever notes it.
     */
    public void takes(Footprint footprint) {
        if (asked != null) {
            asked.addAll(footprint.asked);
        }
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
     * Whether the number {@code node} names can be read beside what this comparison has met
     * ({@link #admits(ElementsNamed)}), by the elements it is read of here.
     */
    public boolean admits(Core node, InputReads at, DeclarationNewtypes newtypes) {
        return !holding || admits(at.elementsNamedIn(node, newtypes));
    }

    /**
     * Whether a number read of the elements {@code named} can be read beside what this comparison
     * has met: it can where each element it reads is read through one name, the one that stands
     * for that element here or the first to, and none through a name whose element is not known.
     */
    public boolean admits(ElementsNamed named) {
        if (!holding) {
            return true;
        }
        if (asked != null) {
            asked.addAll(named.named().keySet());
            asked.addAll(named.unnamed());
        }
        if (named.readsNoOneValue()) {
            crowded = true;
            return false;
        }
        for (Map.Entry<Slot, Set<BindingId>> each : named.named().entrySet()) {
            BindingId name = each.getValue().iterator().next();
            BindingId had = standingFor.putIfAbsent(each.getKey(), name);
            if (had != null && !had.equals(name)) {
                crowded = true;
                return false;
            }
        }
        return true;
    }

    /** Whether a number was refused because it named another element of a container this
     *  comparison was already read of. */
    public boolean crowded() {
        return crowded;
    }
}
