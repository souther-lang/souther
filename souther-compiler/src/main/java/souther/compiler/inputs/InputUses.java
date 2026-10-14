package souther.compiler.inputs;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.partition.InputUse;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Which positions of one behavior's input what the behavior states reads, as far as that is known.
 *
 * <p>Read off the same trees under the same names as {@link InputDemand}, and a different question
 * of them. A demand is every location named, a value a field is read off among them; this tells a
 * value read for what it is apart from one read only to take a field off it, because the second
 * reads that field and none of the value's others.
 *
 * <p><b>Over-approximating what is read is allowed and the other way is not.</b> A position said to
 * be read that a run never reaches leaves a row owed that need not be. A position said not to be
 * read that something reads excuses a row that checks something. So every way a value of the input
 * can go somewhere is taken as reading it whole, except one: a field taken off a value that stands
 * at a position, which stands at a position of its own.
 *
 * <p><b>A value of the input enters a tree only as a parameter.</b> Every other name stands for
 * something the tree computed, and what it computed it out of was walked where it was computed. So a
 * read of a parameter that names no position is the one place a value could go unrecorded, and where
 * one is met nothing here is known.
 *
 * @param named the positions read in part or whole, each at the place a read names
 * @param whole the positions whose value was read as it is, which reads everything under it
 * @param known whether every tree the behavior states was walked and every read of a parameter
 *              named a position
 */
public record InputUses(List<TermPath> named, List<TermPath> whole, boolean known) {

    /** A behavior whose reads are not known: one with no body, or one not walked. */
    public static final InputUses NOT_KNOWN = new InputUses(List.of(), List.of(), false);

    /** A behavior that states nothing reading its input, which a tree may add to. */
    public static final InputUses NOTHING = new InputUses(List.of(), List.of(), true);

    public InputUses {
        named = List.copyOf(new LinkedHashSet<>(named));
        whole = List.copyOf(new LinkedHashSet<>(whole));
    }

    /**
     * Whether the value at {@code position} is read.
     *
     * <p>Read where something at or under it is named, since a read of a field under a case reads
     * which case it is, and where something above it is read whole. Something above it named and
     * not read whole had a field taken off it, and which field is among {@link #named}.
     */
    public InputUse at(TermPath position) {
        if (!known) {
            return new InputUse.NotKnown();
        }
        for (TermPath each : named) {
            if (atOrUnder(each, position)) {
                return new InputUse.Read();
            }
        }
        for (TermPath each : whole) {
            if (atOrUnder(each, position) || atOrUnder(position, each)) {
                return new InputUse.Read();
            }
        }
        return new InputUse.NotRead();
    }

    /**
     * Whether {@code one} is {@code other} or under it, whichever cases either is narrowed to.
     *
     * <p>A field every case of a sum has is read without saying which case, and stands at a
     * position of each. Compared with the cases in, that read would be under none of them, and a
     * position it reads would be said to be read by nothing. Compared without them, a read under
     * one case counts for the position under another as well, which says more is read than is and
     * owes a row that need not be.
     */
    private static boolean atOrUnder(TermPath one, TermPath other) {
        if (!one.head().equals(other.head())) {
            return false;
        }
        List<TermPath.Step> mine = withoutCases(one);
        List<TermPath.Step> theirs = withoutCases(other);
        return mine.size() >= theirs.size() && mine.subList(0, theirs.size()).equals(theirs);
    }

    private static List<TermPath.Step> withoutCases(TermPath path) {
        return path.steps().stream().filter(step -> !(step instanceof TermPath.Step.Refine))
                .toList();
    }

    /** What both read, and known only where both are. */
    public InputUses and(InputUses other) {
        List<TermPath> bothNamed = new ArrayList<>(named);
        bothNamed.addAll(other.named);
        List<TermPath> bothWhole = new ArrayList<>(whole);
        bothWhole.addAll(other.whole);
        return new InputUses(bothNamed, bothWhole, known && other.known);
    }

    /**
     * What {@code tree} reads of the input, under {@code names}.
     *
     * @param parameters the bindings a value of the input enters {@code tree} by
     */
    public static InputUses of(Core tree, InputReads names, Set<BindingId> parameters,
                               Symbols symbols, DeclarationNewtypes newtypes) {
        Walk walk = new Walk(parameters, symbols, newtypes);
        walk.whole(tree, names);
        return new InputUses(List.copyOf(walk.named), List.copyOf(walk.whole), walk.known);
    }

    private static final class Walk {

        private final Set<BindingId> parameters;
        private final Symbols symbols;
        private final DeclarationNewtypes newtypes;
        private final Set<TermPath> named = new LinkedHashSet<>();
        private final Set<TermPath> whole = new LinkedHashSet<>();
        private boolean known = true;

        Walk(Set<BindingId> parameters, Symbols symbols, DeclarationNewtypes newtypes) {
            this.parameters = parameters;
            this.symbols = symbols;
            this.newtypes = newtypes;
        }

        /** {@code e}, whose value goes wherever its parent takes it. */
        void whole(Core e, InputReads names) {
            switch (names.pathOf(e, newtypes)) {
                case PathResolution.At(var at) -> {
                    whole.add(at);
                    // A projection's shorter projections are not children, and each names the
                    // position a field further on is taken off.
                    for (Core standing : Core.subexpressionsAt(e)) {
                        if (standing != e && names.pathOf(standing, newtypes)
                                instanceof PathResolution.At(var shorter)) {
                            named.add(shorter);
                        }
                    }
                    // A field taken off a value at a position reads that field. The value it was
                    // taken off is read for nothing else, so it is walked for the names on the way
                    // and not as a value.
                    if (fieldOf(e) instanceof Core base) {
                        namesOnly(base, names);
                        return;
                    }
                }
                // Each of them on some run, so each is read.
                case PathResolution.MayStandAt(var among) -> whole.addAll(among);
                case PathResolution.NotAPosition _ -> {
                    if (Core.withoutStanding(e) instanceof Core.Read read
                            && parameters.contains(read.binding())) {
                        known = false;
                    }
                }
            }
            ScopeStep.forEachChild(e, (child, step) ->
                    whole(child, names.entering(step, symbols, newtypes)));
        }

        /**
         * {@code e}, which a field is taken off and nothing else is done with.
         *
         * <p>Only where it stands at a position. One that does not is a value computed out of
         * something, and what that is read whole.
         */
        private void namesOnly(Core e, InputReads names) {
            if (!(names.pathOf(e, newtypes) instanceof PathResolution.At(var at))) {
                whole(e, names);
                return;
            }
            named.add(at);
            if (fieldOf(e) instanceof Core base) {
                namesOnly(base, names);
            } else if (!(Core.withoutStanding(e) instanceof Core.Read)) {
                ScopeStep.forEachChild(e, (child, step) ->
                        whole(child, names.entering(step, symbols, newtypes)));
            }
        }

        /** What {@code e} takes a field off, or null where it takes none. */
        private static Core fieldOf(Core e) {
            return switch (Core.withoutStanding(e)) {
                case Core.FieldAccess it -> it.target();
                case Core.FieldProjection it -> it.base();
                default -> null;
            };
        }
    }
}
