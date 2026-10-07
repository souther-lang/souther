package souther.compiler.inputs;

import souther.compiler.core.Core;
import souther.compiler.types.ResolvedCase;

import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;
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
 * <p>Held in one order whatever order the atoms were met in, so that two writings of one set are one
 * value and spell one way.
 */
public final class CasesLeft {

    private final List<Refinement> atoms;

    private CasesLeft(List<Refinement> atoms) {
        TreeSet<Refinement> ordered = new TreeSet<>(CasesLeft::compareAtoms);
        ordered.addAll(atoms);
        if (ordered.isEmpty()) {
            throw new IllegalArgumentException("a value left no case is no value");
        }
        if (ordered.first().getClass() != ordered.last().getClass()) {
            throw new IllegalArgumentException("the cases of a sum and an optional's carriers are"
                    + " distinctions of two positions, never alternatives at one: " + ordered);
        }
        this.atoms = List.copyOf(ordered);
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

    /** What a value may be, in the one order these are held in. */
    public List<Refinement> atoms() {
        return atoms;
    }

    /** The one distinction this leaves, or null where it leaves several. */
    public Refinement only() {
        return atoms.size() == 1 ? atoms.getFirst() : null;
    }

    /** What a value both leave may be, or null where they leave it nothing in common. */
    public CasesLeft meet(CasesLeft other) {
        List<Refinement> both = new ArrayList<>(atoms);
        both.retainAll(other.atoms);
        return both.isEmpty() ? null : new CasesLeft(both);
    }

    /** The atoms of this {@code kept} keeps, or null where it keeps none. */
    public CasesLeft keeping(Predicate<Refinement> kept) {
        List<Refinement> out = atoms.stream().filter(kept).toList();
        return out.isEmpty() ? null : new CasesLeft(out);
    }

    /** Whether every value this leaves is one {@code wider} leaves as well. */
    public boolean within(CasesLeft wider) {
        return wider.atoms.containsAll(atoms);
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

    /** One order for these that ties no two that are not equal: atom by atom, and then the shorter
     *  first. */
    static int compare(CasesLeft one, CasesLeft other) {
        int common = Math.min(one.atoms.size(), other.atoms.size());
        for (int at = 0; at < common; at++) {
            int byAtom = compareAtoms(one.atoms.get(at), other.atoms.get(at));
            if (byAtom != 0) {
                return byAtom;
            }
        }
        return Integer.compare(one.atoms.size(), other.atoms.size());
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
        return other instanceof CasesLeft that && atoms.equals(that.atoms);
    }

    @Override
    public int hashCode() {
        return atoms.hashCode();
    }

    @Override
    public String toString() {
        return "CasesLeft" + atoms;
    }
}
