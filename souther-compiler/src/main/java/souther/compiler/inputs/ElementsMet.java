package souther.compiler.inputs;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
            BindingId had = standingFor.putIfAbsent(new Slot(stood.container(), stood.part()),
                    stood.name());
            if (had != null && !had.equals(stood.name())) {
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
