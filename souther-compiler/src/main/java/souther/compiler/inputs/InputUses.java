package souther.compiler.inputs;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.partition.InputUse;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Which positions of one behavior's input what the behavior states reads, as far as that is known.
 *
 * <p>Read off a tree in the walk that finds its {@link InputDemand}, and a different question of
 * it. A demand is every location named, a value a field is read off among them; this tells a value
 * read for what it is apart from one read only to take a field off it, because the second reads
 * that field and none of the value's others. One walk for both, so the nodes are met and placed
 * once.
 *
 * <p><b>Over-approximating what is read is allowed and the other way is not.</b> A position said to
 * be read that a run never reaches leaves a row owed that need not be. A position said not to be
 * read that something reads excuses a row that checks something. So every way a value of the input
 * can go somewhere is taken as reading it whole, except three. A field taken off a value at a
 * position reads that field. A name bound to a value at a position reads nothing by being bound,
 * because every read of the name is placed at the position as the reads of the input are
 * ({@link InputReads}). And a {@code match} on a value at a position asks which case it is, which
 * reads the position and nothing under it; what an arm reads further is read through the name it
 * binds.
 *
 * <p><b>A value of the input enters a tree only under a name, and every such name is watched.</b>
 * A parameter, and a name this walk bound to a position without reading it. Every other name stands
 * for something the tree computed, and what it computed it out of was walked where it was computed.
 * So a read of a watched name that names no position is the one place a value could go unrecorded,
 * and where one is met nothing here is known.
 *
 * <p><b>Held without the cases on the way.</b> A field every case of a sum has is read without
 * saying which case, and stands at a position of each. Compared with the cases in, that read would
 * be under none of them, and a position it reads would be said to be read by nothing. Compared
 * without them, a read under one case counts for the position under another as well, which says
 * more is read than is and owes a row that need not be. Taken out once here, and once of the
 * position asked about, rather than at every comparison.
 *
 * @param decided the positions a {@code match} asks which case they are, which reads each of them
 *                and nothing under it
 * @param whole   the positions whose value was read as it is, which reads everything under it
 * @param known   whether every tree the behavior states was walked and every read of a watched
 *                name named a position
 */
public record InputUses(List<TermPath> decided, List<TermPath> whole, boolean known) {

    /** A behavior whose reads are not known: one with no body, or one not walked. */
    public static final InputUses NOT_KNOWN = new InputUses(List.of(), List.of(), false);

    /** A behavior that states nothing reading its input, which a tree may add to. */
    public static final InputUses NOTHING = new InputUses(List.of(), List.of(), true);

    public InputUses {
        decided = withoutCases(decided);
        whole = withoutCases(whole);
    }

    /**
     * Whether the value at {@code position} is read.
     *
     * <p>Read where something at or under it is read, since a read under a case reads which case it
     * is, and where something above it is read whole. Something above it asked only which case it
     * is says nothing about what the case holds.
     */
    public InputUse at(TermPath position) {
        if (!known) {
            return new InputUse.NotKnown();
        }
        TermPath asked = withoutCases(position);
        for (TermPath each : decided) {
            if (each.isAtOrUnder(asked)) {
                return new InputUse.Read();
            }
        }
        for (TermPath each : whole) {
            if (each.isAtOrUnder(asked) || asked.isAtOrUnder(each)) {
                return new InputUse.Read();
            }
        }
        return new InputUse.NotRead();
    }

    /** What both read, and known only where both are. */
    public InputUses and(InputUses other) {
        List<TermPath> bothDecided = new ArrayList<>(decided);
        bothDecided.addAll(other.decided);
        List<TermPath> bothWhole = new ArrayList<>(whole);
        bothWhole.addAll(other.whole);
        return new InputUses(bothDecided, bothWhole, known && other.known);
    }

    private static List<TermPath> withoutCases(List<TermPath> paths) {
        Set<TermPath> out = new LinkedHashSet<>();
        for (TermPath each : paths) {
            out.add(withoutCases(each));
        }
        return List.copyOf(out);
    }

    private static TermPath withoutCases(TermPath path) {
        if (path.steps().stream().noneMatch(step -> step instanceof TermPath.Step.Refine)) {
            return path;
        }
        return new TermPath(path.head(), path.steps().stream()
                .filter(step -> !(step instanceof TermPath.Step.Refine)).toList());
    }

    /**
     * What one walk of a tree found: every location it names, in the order they were met, and
     * which of them it reads.
     */
    public record Walked(InputDemand demand, InputUses uses) {}

    /**
     * What {@code tree} names and reads of the input, under {@code names}.
     *
     * @param parameters the bindings a value of the input enters {@code tree} by
     */
    public static Walked of(Core tree, InputReads names, Set<BindingId> parameters,
                            Symbols symbols, DeclarationNewtypes newtypes) {
        Walk walk = new Walk(parameters, symbols, newtypes);
        walk.whole(tree, names);
        return new Walked(new InputDemand(List.copyOf(walk.demanded)),
                new InputUses(List.copyOf(walk.decided), List.copyOf(walk.whole), walk.known));
    }

    private static final class Walk {

        /** The names a value of the input may be read under: the parameters, and every name this
         *  walk bound to a position without reading it. */
        private final Set<BindingId> watched;
        private final Symbols symbols;
        private final DeclarationNewtypes newtypes;
        private final Set<TermPath> demanded = new LinkedHashSet<>();
        private final Set<TermPath> decided = new LinkedHashSet<>();
        private final Set<TermPath> whole = new LinkedHashSet<>();
        private boolean known = true;

        Walk(Set<BindingId> parameters, Symbols symbols, DeclarationNewtypes newtypes) {
            this.watched = new HashSet<>(parameters);
            this.symbols = symbols;
            this.newtypes = newtypes;
        }

        /** {@code e}, whose value goes wherever its parent takes it. */
        void whole(Core e, InputReads names) {
            // Every subexpression and not only the node: a projection's shorter projections are
            // not children, and each names a position as the access over it does.
            for (Core each : Core.subexpressionsAt(e)) {
                note(each, names);
            }
            switch (names.pathOf(e, newtypes)) {
                case PathResolution.At(var at) -> {
                    whole.add(at);
                    // A field taken off a value at a position reads that field. The value it was
                    // taken off is read for nothing else, so it is walked for the names on the way
                    // and not as a value.
                    if (fieldOf(e) instanceof Core base) {
                        takenOff(base, names);
                        return;
                    }
                }
                // Each of them on some run, so each is read.
                case PathResolution.MayStandAt(var among) -> whole.addAll(among);
                case PathResolution.NotAPosition _ -> {
                    if (Core.withoutStanding(e) instanceof Core.Read read
                            && watched.contains(read.binding())) {
                        known = false;
                    }
                }
            }
            Core held = heldWithoutReading(e, names);
            ScopeStep.forEachChild(e, (child, step) -> {
                InputReads inside = names.entering(step, symbols, newtypes);
                if (child == held) {
                    takenOff(child, inside);
                } else {
                    whole(child, inside);
                }
            });
        }

        /**
         * {@code e}, which stands at a position and is read for nothing but a field taken off it,
         * a name bound to it, or which case it is.
         *
         * <p>Only where it stands at a position. One that does not is a value computed out of
         * something, and what that is read whole.
         */
        private void takenOff(Core e, InputReads names) {
            if (!(names.pathOf(e, newtypes) instanceof PathResolution.At)) {
                whole(e, names);
                return;
            }
            for (Core each : Core.subexpressionsAt(e)) {
                note(each, names);
            }
            if (fieldOf(e) instanceof Core base) {
                takenOff(base, names);
            } else if (e instanceof Core.Widen standingAs) {
                // The same value standing as a wider type, which a field is taken off all the same.
                takenOff(standingAs.value(), names);
            } else {
                ScopeStep.forEachChild(e, (child, step) ->
                        whole(child, names.entering(step, symbols, newtypes)));
            }
        }

        /**
         * The child of {@code e} that is not read by being there, or null where every child is.
         *
         * <p>The value a {@code let} binds, where it stands at a position: the name stands there
         * in the body, and what the body reads of it is read through the name. And the value a
         * {@code match} asks, where it stands at a position: which case it is, which reads that
         * position, and what each arm reads of it is read through the name the arm binds. Either
         * name is watched from here on.
         */
        private Core heldWithoutReading(Core e, InputReads names) {
            if (e instanceof Core.LetIn binding
                    && names.pathOf(binding.value(), newtypes) instanceof PathResolution.At) {
                watch(binding.binder());
                return binding.value();
            }
            if (e instanceof Core.Match choice
                    && names.pathOf(choice.scrutinee(), newtypes)
                            instanceof PathResolution.At(var at)) {
                decided.add(at);
                for (Core.Case arm : choice.cases()) {
                    watch(arm.binding().binder());
                }
                return choice.scrutinee();
            }
            return null;
        }

        private void watch(Core.Binder binder) {
            if (binder != null && binder.binding() != null) {
                watched.add(binder.binding());
            }
        }

        /**
         * Where {@code each} stands, which is a location the demand names. What it reads is asked
         * where it is walked.
         */
        private void note(Core each, InputReads names) {
            switch (names.pathOf(each, newtypes)) {
                case PathResolution.At(var at) -> demanded.add(at);
                case PathResolution.NotAPosition _ -> { }
                // A name that may stand at a place stands there on some run, so each is named.
                case PathResolution.MayStandAt(var among) -> demanded.addAll(among);
            }
        }

        /**
         * What {@code e} takes a field off, or null where it takes none. A value standing as a
         * wider type takes none itself, and what it stands for is its child.
         */
        private static Core fieldOf(Core e) {
            if (e instanceof Core.Widen) {
                return null;
            }
            return switch (e) {
                case Core.FieldAccess it -> it.target();
                case Core.FieldProjection it -> it.base();
                default -> null;
            };
        }
    }
}
