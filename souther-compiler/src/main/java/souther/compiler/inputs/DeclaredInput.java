package souther.compiler.inputs;

import souther.compiler.check.AtomSpace;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.ReadableFields;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Set;
import java.util.Map;
import java.util.Objects;

/**
 * What a behavior's declaration puts at a path of its input, read off the declarations alone.
 *
 * <p>Not a reading of the input. Which positions the input has and what its rules leave at them is
 * {@link InputDomain}'s, and that reading is built over the paths a body names — so whatever names
 * them runs before there is one. What the declarations say a path holds needs nothing of the
 * kind: the parameters' types and the declarations under them, both there before anything is read.
 *
 * <p>Which is what lets a walk of a body ask it. An arm narrows the value it matched to the case it
 * selects, and the case is relative to the type the scrutinee stands as there — which is wider than
 * the value wherever the value was handed to a parameter of a wider type. A field declared
 * {@code DecimalPart} matched as a {@code Coefficient} is already the case the arm selects, and
 * written down as a narrowing it is a second spelling of a position the declaration names without
 * one. The two spellings never meet: everything read off the declarations is keyed by the first.
 * So the narrowing is asked of what the declaration puts there ({@link #taking}), and a narrowing
 * the declaration already makes is not written.
 *
 * <p>Asked, not worked out, at each step: what is under a type is read through
 * {@link StructuralInspection}, which is where the walk that makes the positions takes its steps
 * from, and what a value of a type can be is {@link AtomSpace}'s. A reader deciding either for
 * itself would be a second account of the declarations next to the one the reading is made from.
 */
public final class DeclaredInput {

    /** An input of no parameters: every path is under a name it does not declare. */
    public static final DeclaredInput NONE = new DeclaredInput(Map.of(), null);

    private final Map<String, Type> parameters;
    private final RuleReadingSource source;

    private DeclaredInput(Map<String, Type> parameters, RuleReadingSource source) {
        this.parameters = Map.copyOf(parameters);
        this.source = source;
    }

    /** The parameters {@code declared} takes, read under {@code source}. */
    public static DeclaredInput of(DeclaredSig declared, RuleReadingSource source) {
        Map<String, Type> parameters = new LinkedHashMap<>();
        for (DeclaredSig.Input input : declared.inputs()) {
            parameters.putIfAbsent(input.name(), input.type());
        }
        return new DeclaredInput(parameters, Objects.requireNonNull(source));
    }

    /** The same, of the parameters a reading of the input was made from. */
    static DeclaredInput of(List<InputDomain.Parameter> declared, RuleReadingSource source) {
        Map<String, Type> parameters = new LinkedHashMap<>();
        for (InputDomain.Parameter parameter : declared) {
            parameters.putIfAbsent(parameter.name(), parameter.type());
        }
        return new DeclaredInput(parameters, Objects.requireNonNull(source));
    }

    /**
     * What arriving at {@code at} by an arm leaving the value {@code covered} says of the value
     * there, the arm being written over a scrutinee that stands as {@code matchedAs}.
     *
     * <p>Asked of the arm's selection whole, as the leaves it covers ({@link CasesLeft#selectedBy}),
     * and never of one narrowing made out of it first. A case that is itself a sum covers several
     * leaves, and so does an arm naming several cases; a reader that had turned either into one
     * narrowing before asking would find nothing to ask about — even where the declaration leaves
     * the value no leaf outside them, so that the arm narrows nothing at all.
     *
     * <p>The declaration may leave the value only leaves the arm covers, and then arriving says
     * nothing: the position is the one the declaration names, spelled the way it does. It may leave
     * the value none of them, and then no value at the position arrives that way. Otherwise arriving
     * says which of the leaves it turned out to be, and those are the leaves the arm covers that the
     * declaration leaves — one or several, written into the path either way. An arm naming
     * {@code OnceKind} over a field declared {@code VisitKind} leaves {@code Station} or
     * {@code Hospital}; over a field declared {@code Station | Renkei} it leaves {@code Station},
     * and is spelled as an arm naming {@code Station} is.
     *
     * <p>A position already narrowed to several leaves is read as those leaves, which is what the
     * declaration leaves there now; and an arm narrowing it further narrows that narrowing rather
     * than adding a second one after it ({@link #narrowedTo}).
     *
     * <p>What the declaration leaves the value is read under each name it wears as well as under
     * all of them, because the path does not say how many of them the scrutinee took off: taking a
     * newtype's {@code value} is no step. A field declared {@code Open = Flag} is matched as the
     * {@code Flag} under the name at the same path a field declared {@code WholeDigits} is matched
     * as the case it is. Which of those readings the arm can be matching is what {@code matchedAs}
     * settles: the scrutinee stands as a type whose leaves hold the value it was given, so a reading
     * leaving the value something outside them is not the one the arm is over. A newtype is no sum,
     * so each name is the one value it is, and what is under the last of them is what
     * {@link AtomSpace} says it can be.
     *
     * <p>As the arm says it wherever the declarations say nothing this can follow, which is the
     * answer a reader was given before the declarations were asked.
     */
    public Taking taking(TermPath at, Type matchedAs, CasesLeft covered) {
        Taking asTheArmSaysIt = new Taking.Narrows(narrowedTo(at, covered));
        List<List<TypeSymbol>> readings = readingsAt(at);
        List<TypeSymbol> chosen = leavesOf(covered.atoms());
        if (readings == null || matchedAs == null || chosen.isEmpty()) {
            return asTheArmSaysIt;
        }
        Set<TypeSymbol> matchable = new HashSet<>(
                AtomSpace.subjectAtoms(matchedAs, source.kinds(), source.sums()));
        boolean reaches = false;
        boolean within = true;
        boolean read = false;
        Set<TypeSymbol> left = new HashSet<>();
        for (List<TypeSymbol> leaves : readings) {
            if (leaves.isEmpty() || !matchable.containsAll(leaves)) {
                continue;
            }
            read = true;
            reaches |= leaves.stream().anyMatch(chosen::contains);
            within &= chosen.containsAll(leaves);
            left.addAll(leaves);
        }
        if (!read) {
            return asTheArmSaysIt;
        }
        if (!reaches) {
            return new Taking.Excluded();
        }
        if (within) {
            return new Taking.Implied();
        }
        // The leaves the arm covers that the declaration leaves, which is not empty: the arm
        // reaches one of them.
        CasesLeft both = covered.keeping(each -> each instanceof Refinement.SumCase sum
                && left.contains(sum.leaf()));
        return new Taking.Narrows(narrowedTo(at, both));
    }

    /**
     * {@code at} narrowed to {@code cases}.
     *
     * <p>Narrowing a position already narrowed to several leaves to some of them is one narrowing
     * of it, stronger, and not a second narrowing after the first: {@code kind@{Hospital|Station}}
     * narrowed to {@code Station} is {@code kind@Station}, which is the position the reading of
     * the input holds and the one an arm naming {@code Station} outright arrives at. A step after
     * it would be a location nothing else spells.
     *
     * <p>Only from several leaves. A position narrowed to one distinction and narrowed again is a
     * distinction of what stands there — an optional inside an optional, a newtype case over a sum
     * — and folding the two would lose the outer one.
     */
    public static TermPath narrowedTo(TermPath at, CasesLeft cases) {
        return at.narrowsWhatItReaches() && at.narrowing().only() == null
                && cases.within(at.narrowing())
                ? at.narrowedFrom().refine(cases) : at.refine(cases);
    }

    /**
     * What a value at {@code at} can be, as {@link #readingsOf} reads it, or null where the
     * declarations put nothing this can follow there.
     *
     * <p>A position narrowed to several leaves is those leaves: the declaration put a sum there and
     * the narrowing left this much of it.
     */
    private List<List<TypeSymbol>> readingsAt(TermPath at) {
        if (at.narrowsWhatItReaches() && at.narrowing().only() == null) {
            return List.of(leavesOf(at.narrowing().atoms()));
        }
        Type here = typeAt(at);
        return here == null ? null : readingsOf(here);
    }

    /** The leaves {@code covered} narrows to, or none where it narrows to something that is not a
     *  case of a sum. */
    private static List<TypeSymbol> leavesOf(List<Refinement> covered) {
        List<TypeSymbol> out = new ArrayList<>();
        for (Refinement each : covered) {
            switch (each) {
                case Refinement.SumCase sum -> out.add(sum.leaf());
                // An optional's carriers are no leaves of anything a declaration can already have
                // settled: nothing stands as an optional that was handed something narrower.
                case Refinement.Presence _ -> {
                    return List.of();
                }
            }
        }
        return out;
    }

    /**
     * What a value of {@code type} can be, once under each name it wears and once under all of
     * them: the outermost name first, and what is under the last name at the end.
     */
    private List<List<TypeSymbol>> readingsOf(Type type) {
        TypeOps.NewtypeSpine spine = TypeOps.newtypeSpine(type, source.inners());
        List<List<TypeSymbol>> out = new ArrayList<>();
        spine.layers().forEach(layer -> out.add(List.of(layer.named())));
        out.add(AtomSpace.subjectAtoms(spine.terminal(), source.kinds(), source.sums()));
        return out;
    }

    /** What arriving at a position by an arm says of the value there ({@link #taking}). */
    public sealed interface Taking {

        /**
         * The declaration leaves the value more than the leaves the arm covers, and this is the
         * position read as the ones it leaves of them.
         *
         * <p>One answer however many leaves that is. How many is what the narrowing at the end of
         * {@code to} says, and a reader with nothing to do with the difference has no second shape
         * to tell it.
         */
        record Narrows(TermPath to) implements Taking {

            public Narrows {
                if (to == null || !to.narrowsWhatItReaches()) {
                    throw new IllegalArgumentException(
                            "an arm that narrows reads a position as some of its cases: " + to);
                }
            }
        }

        /** The declaration leaves the value only leaves the arm covers, so arriving says nothing. */
        record Implied() implements Taking {}

        /** The declaration leaves the value none of the leaves the arm covers, so no value there
         *  arrives this way. */
        record Excluded() implements Taking {}
    }

    /**
     * What the declarations put at {@code path}, however far down it goes, or null where they put
     * nothing this can follow.
     *
     * <p>Step by step through {@link StructuralInspection}, which is what the walk making the
     * positions takes its own steps from. What is under a type is one fact, and a second reading of
     * it here would be this and that walk disagreeing about what a path reaches. A path is finite
     * and each step of it is followed once, so following one under a declaration that names itself
     * ends where the path does.
     */
    Type typeAt(TermPath path) {
        Type here = parameters.get(path.head());
        for (TermPath.Step step : path.steps()) {
            here = here == null ? null : under(here, step, source);
        }
        return here;
    }

    /**
     * What one step of a path stands at, or null where the declarations put nothing there.
     *
     * <p><b>Exhaustive over the kinds of step, with no {@code default}.</b> A path goes into a
     * field, into what a container holds, into a map's keys, or nowhere at all while narrowing
     * which values may stand where it already is ({@link Refinement}) — and a reading that answered
     * some of them and let the rest fall to null would lose a line the model draws for every path
     * carrying one. Another kind is a compile error here rather than a quiet absence.
     */
    private static Type under(Type type, TermPath.Step step, RuleReadingSource source) {
        // Asked of the shape rather than through the proof a position is made with. What is under a
        // type is a question about the type, and a type nothing can be read at answers nothing here
        // rather than being refused as a position this compiler disagrees with itself about.
        if (!(TypeView.shapeOf(type, source.inners(), source.symbols(), source.kinds(),
                        source.sums())
                instanceof Shape.ReadablePositionShape shape)) {
            return null;
        }
        StructuralInspection under =
                StructuralInspection.of(shape,
                        Distinctions.ofType(shape, source.symbols(), source.kinds(),
                                source.sums()));
        return switch (step) {
            // A field of a record, or a name a sum's cases all spread. The second is readable on a
            // value of the sum without opening a case, so the model does put something at it, and a
            // reading that answered for the first alone would say the model puts nothing where the
            // language reads a value.
            case TermPath.Step.Field field -> under instanceof StructuralInspection.Decomposed made
                    ? made.under().get(field.name())
                    : ReadableFields.of(shape).declaredFields().get(field.name());
            // What a list or a set holds, or the values a map holds under its keys.
            case TermPath.Step.Element _ -> under instanceof StructuralInspection.Retained on
                    ? switch (on.continuation()) {
                        case StructuralInspection.Continuation.Elements held -> held.element();
                        case StructuralInspection.Continuation.Entries entries -> entries.value();
                        case StructuralInspection.Continuation.None _,
                             StructuralInspection.Continuation.Branches _,
                             StructuralInspection.Continuation.Blocked _ -> null;
                    }
                    : null;
            // A map's keys, which only a map has.
            case TermPath.Step.Key _ -> under instanceof StructuralInspection.Retained on
                    && on.continuation() instanceof StructuralInspection.Continuation.Entries entries
                    ? entries.key() : null;
            // The same position, read as the case it turned out to be. Null where the case puts
            // nothing there, which is a case that is the whole of a value — and where it turned
            // out to be one of several, which no one declaration is: what is under each of them is
            // asked of that one ({@link #readingsAt} reads the position itself as its leaves).
            case TermPath.Step.Refine refine -> under instanceof StructuralInspection.Retained on
                    && on.continuation() instanceof StructuralInspection.Continuation.Branches ways
                    && refine.cases().only() != null
                    ? narrowed(ways, refine.cases().only()) : null;
        };
    }

    /** The type the branch for this narrowing stands at, or null where the sum has no such branch. */
    private static Type narrowed(StructuralInspection.Continuation.Branches ways,
                                 Refinement refinement) {
        for (StructuralInspection.Branch branch : ways.branches()) {
            if (refinement.equals(branch.refinement())) {
                return branch.under();
            }
        }
        return null;
    }

    /**
     * Two are one where they declare the same parameters.
     *
     * <p>The source is not compared. It is how the declarations are read rather than what they
     * say, the way {@link InputDomain} holds where it borrows from: one analysis reads one input
     * under one source, and a comparison that walked the scope would cost every reading that holds
     * this as much as the scope is large.
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof DeclaredInput that && parameters.equals(that.parameters);
    }

    @Override
    public int hashCode() {
        return parameters.hashCode();
    }

    @Override
    public String toString() {
        return "DeclaredInput" + parameters;
    }
}
