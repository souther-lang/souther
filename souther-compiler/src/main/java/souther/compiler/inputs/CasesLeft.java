package souther.compiler.inputs;

import souther.compiler.core.Core;
import souther.compiler.types.ResolvedCase;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

/**
 * Which of a position's distinctions a value standing there may still be: one of them, or several.
 *
 * <p>Above {@link Refinement} and not a second kind of it. A refinement is one distinction — one
 * leaf of a sum, or an optional holding something or nothing — and every reader that builds a value
 * or walks the branches under a position needs exactly one: a {@code Station} is built, and
 * "{@code Station} or {@code Hospital}" is not something to build. What a condition establishes is
 * wider than that. An arm naming a case that is itself a sum leaves the value any of the leaves
 * under it, and a position read under that arm is narrowed without being narrowed to one of them.
 * So the atom stays what it is, and this is the set of atoms a value is left.
 *
 * <p><b>Put together by intersection, and by nothing else.</b> Two conditions that each leave a
 * position some of its distinctions leave it the ones both do: the outer arm leaving
 * {@code Station} or {@code Hospital} and the inner one leaving {@code Station} leave
 * {@code Station}, and only two that share none leave nothing. Equality is the special case of one
 * atom on each side.
 *
 * <p><b>One kind of distinction at a time.</b> The leaves of a sum and an optional's two carriers
 * are distinctions of different positions, never alternatives of one, so a set holding one of each
 * is a value this refuses rather than one every reader has to decide what to do with.
 *
 * <p><b>Compared as a set, and held in the order the model declares the cases.</b> Two writings of
 * one set are one value whatever order either met the atoms in. The order they are held and spelled
 * in is the declaration's where the reader knows it ({@link DeclaredInput#taking}) and the order the
 * selection reaches them otherwise, which is the declaration's order of the cases under one case.
 * Never the order the names compare in: a model whose cases were renamed is the same model, and
 * what it says about them reads the same way round.
 */
public final class CasesLeft {

    private final List<Refinement> atoms;

    /** The same atoms as a set, which is what tells two of these apart. */
    private final Set<Refinement> members;

    private CasesLeft(List<Refinement> atoms) {
        Set<Refinement> once = new LinkedHashSet<>(atoms);
        if (once.isEmpty()) {
            throw new IllegalArgumentException("a value left no case is no value");
        }
        if (once.stream().map(Object::getClass).distinct().count() > 1) {
            throw new IllegalArgumentException("the cases of a sum and an optional's carriers are"
                    + " distinctions of two positions, never alternatives at one: " + once);
        }
        this.atoms = List.copyOf(once);
        this.members = Set.copyOf(once);
    }

    /** Exactly {@code one}. */
    public static CasesLeft of(Refinement one) {
        return new CasesLeft(List.of(one));
    }

    /** Every distinction selecting {@code selected} covers ({@link Refinement#allOf}). */
    public static CasesLeft of(ResolvedCase selected) {
        return new CasesLeft(Refinement.allOf(selected));
    }

    /**
     * What an arm selecting {@code pattern} leaves the value it matched, or null where it leaves no
     * set of distinctions of one position.
     *
     * <p>The arm's whole selection, so that an arm naming {@code OnceKind} and one naming
     * {@code Station | Hospital} leave the value the same thing: the leaves each case covers, put
     * together. An or-pattern over an optional's carriers is the other kind of answering for several,
     * and leaves nothing an optional's position is narrowed to — the two carriers are all an optional
     * holds — so it is not one.
     */
    public static CasesLeft selectedBy(Core.ResolvedPattern pattern) {
        return switch (pattern) {
            case Core.ResolvedPattern.Single one -> of(one.selected());
            case Core.ResolvedPattern.AnyOf several -> {
                List<Refinement> covered = new ArrayList<>();
                for (ResolvedCase each : several.cases()) {
                    if (!(each.refinement()
                            instanceof souther.compiler.types.Refinement.Direct)) {
                        yield null;
                    }
                    covered.addAll(Refinement.allOf(each));
                }
                yield new CasesLeft(covered);
            }
        };
    }

    /** What a value may be, in the order the model declares them. */
    public List<Refinement> atoms() {
        return atoms;
    }

    /**
     * The same cases, held in the order {@code declared} writes the leaves.
     *
     * <p>For the reader that knows what a position's declaration divides it into: a selection
     * written over several cases reaches them in the order it was written, and that is the author's
     * order and not the model's. Leaves {@code declared} does not name keep their place after the
     * ones it does.
     */
    CasesLeft orderedAs(List<TypeSymbol> declared) {
        List<Refinement> out = new ArrayList<>();
        for (TypeSymbol leaf : declared) {
            for (Refinement each : atoms) {
                if (each instanceof Refinement.SumCase sum && sum.leaf().equals(leaf)) {
                    out.add(each);
                }
            }
        }
        for (Refinement each : atoms) {
            if (!out.contains(each)) {
                out.add(each);
            }
        }
        return new CasesLeft(out);
    }

    /** The one distinction this leaves, or null where it leaves several. */
    public Refinement only() {
        return atoms.size() == 1 ? atoms.getFirst() : null;
    }

    /** What a value both leave may be, or null where they leave it nothing in common. */
    public CasesLeft meet(CasesLeft other) {
        List<Refinement> both = new ArrayList<>(atoms);
        both.retainAll(other.members);
        return both.isEmpty() ? null : new CasesLeft(both);
    }

    /** The atoms of this {@code kept} keeps, or null where it keeps none. */
    public CasesLeft keeping(Predicate<Refinement> kept) {
        List<Refinement> out = atoms.stream().filter(kept).toList();
        return out.isEmpty() ? null : new CasesLeft(out);
    }

    /** Whether this leaves a value the case {@code leaf} of a sum. */
    public boolean leaves(TypeSymbol leaf) {
        return atoms.stream().anyMatch(each -> each instanceof Refinement.SumCase sum
                && sum.leaf().equals(leaf));
    }

    /** Whether every value this leaves is one {@code wider} leaves as well. */
    public boolean within(CasesLeft wider) {
        return wider.members.containsAll(members);
    }

    /**
     * How a path writes it: the one atom as it is written, and several between braces.
     *
     * <p>The single atom is spelled as the atom, so a position narrowed to one case is written the
     * way the reading of the input names it.
     */
    public String spelled() {
        return only() != null ? only().spelled()
                : atoms.stream().map(Refinement::spelled)
                        .collect(Collectors.joining("|", "{", "}"));
    }

    /** The same, with which kind of narrowing it is said as well ({@link Refinement#discriminated}). */
    public String discriminated() {
        return only() != null ? only().discriminated()
                : atoms.stream().map(Refinement::discriminated)
                        .collect(Collectors.joining("|", "{", "}"));
    }

    /**
     * One order for these that ties no two that are not equal: the atoms of each in one order,
     * compared atom by atom, and then the shorter first.
     *
     * <p>The atoms sorted for this and not as they are held, because two equal sets may be held in
     * two orders and an order over values has to tie them.
     */
    static int compare(CasesLeft one, CasesLeft other) {
        List<Refinement> mine = one.atoms.stream().sorted(CasesLeft::compareAtoms).toList();
        List<Refinement> theirs = other.atoms.stream().sorted(CasesLeft::compareAtoms).toList();
        int common = Math.min(mine.size(), theirs.size());
        for (int at = 0; at < common; at++) {
            int byAtom = compareAtoms(mine.get(at), theirs.get(at));
            if (byAtom != 0) {
                return byAtom;
            }
        }
        return Integer.compare(mine.size(), theirs.size());
    }

    /**
     * One order for atoms that ties no two that are not equal: the sum's leaves before an optional's
     * carriers, each by what it narrows to.
     */
    private static int compareAtoms(Refinement one, Refinement other) {
        return switch (one) {
            case Refinement.SumCase sum -> other instanceof Refinement.SumCase that
                    ? sum.leaf().compareTo(that.leaf()) : -1;
            case Refinement.Presence presence -> other instanceof Refinement.Presence that
                    ? Boolean.compare(presence.present(), that.present()) : 1;
        };
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof CasesLeft that && members.equals(that.members);
    }

    @Override
    public int hashCode() {
        return members.hashCode();
    }

    @Override
    public String toString() {
        return "CasesLeft" + atoms;
    }
}
