package souther.compiler.check;

import souther.compiler.core.BoundaryCheck;
import souther.compiler.core.BoundaryConstraint;
import souther.compiler.core.BoundaryConstraint.DecimalMax;
import souther.compiler.core.BoundaryConstraint.DecimalMin;
import souther.compiler.core.BoundaryConstraint.DecimalNonNegative;
import souther.compiler.core.BoundaryConstraint.DecimalPositive;
import souther.compiler.core.BoundaryConstraint.FixedLength;
import souther.compiler.core.BoundaryConstraint.FixedSize;
import souther.compiler.core.BoundaryConstraint.MapMaxSize;
import souther.compiler.core.BoundaryConstraint.MapMinSize;
import souther.compiler.core.BoundaryConstraint.Max;
import souther.compiler.core.BoundaryConstraint.MaxLength;
import souther.compiler.core.BoundaryConstraint.MaxSize;
import souther.compiler.core.BoundaryConstraint.Min;
import souther.compiler.core.BoundaryConstraint.MinLength;
import souther.compiler.core.BoundaryConstraint.MinSize;
import souther.compiler.core.BoundaryConstraint.NonEmpty;
import souther.compiler.core.BoundaryConstraint.NonNegative;
import souther.compiler.core.BoundaryConstraint.Pattern;
import souther.compiler.core.BoundaryConstraint.Positive;
import souther.compiler.core.BoundaryConstraint.Unique;
import souther.compiler.core.Core;
import souther.compiler.core.IntNegation;
import souther.compiler.core.Kernel;
import souther.compiler.core.ValueShape;
import souther.compiler.numeric.EndSide;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Which clauses of a data made of one field the boundary can state as the constraints a decoder
 * names, so a violation carries the rule it broke — a length short of its minimum, a string off its
 * format — instead of one {@code invariant_violation} for every invariant in the model.
 *
 * <p>Only exact equivalences are stated. A constraint weaker than the clause would let through what
 * the clause refuses; one stronger than it would refuse values the domain accepts, and would do so at
 * the boundary where it reads as bad input. Anything this cannot prove equivalent is left to the
 * clause's own condition.
 *
 * <p>Answered here, once, and carried on each clause of the value's shape
 * ({@link ValueShape.Invariant#boundary()}). A backend reads the answer and
 * decides only what its decoder calls each constraint.
 *
 * <p><b>Read off what a statement states, never off the tree it was written as.</b> One rule written
 * out, reached through a helper and written as the denial of its opposite is one statement
 * ({@link InvariantStatement}), and what a decoder reports is public boundary behaviour — so a
 * mapping that turned on the spelling would hand two callers two different codes for one rule of the
 * model. The bindings a helper left and the denial an author wrote are spent where the statement is
 * made, and what arrives here is a claim about two values in that order.
 */
public final class BoundaryConstraints {

    /** The symbols this reads clauses against. Which operations state a constraint is a fact about
     *  the library the clause was resolved against, so it is held here rather than asked at each
     *  call. */
    private final Symbols symbols;

    /** The name of the data's one field, which is how its clauses read it. */
    private final String field;

    private BoundaryConstraints(Symbols symbols, String field) {
        this.symbols = symbols;
        this.field = field;
    }

    /**
     * How the boundary checks each clause that governs {@code named}, a data made of the one field
     * {@code sole}, keyed by which clause it is.
     *
     * <p>A data of one field and not a newtype. The constraints are what a clause says of that
     * field's value, and a newtype and a product of one field hold the same clauses of the same
     * field (spec §newtype), so they are answered alike. Which of the two crosses as the field's
     * value, and so reads these, is decided by the form it was declared in, which this does not
     * ask.
     *
     * <p>Read from the representation the constraints are written against
     * ({@link InliningPolicy#DISCHARGE}): this module's own helpers expanded, the language's own
     * operations left standing. The mapping is about the operations an author wrote —
     * {@code List.length}, {@code List.allDistinctBy} — and in the settled form a prelude helper has
     * become the fold it is derived from, so every collection rule would go unrecognised there.
     *
     * <p>Keyed by the clause and not by position. The clauses a value is checked against are the
     * settled ones, and this is the other representation of the same clauses; the key is what says
     * the two answers are about one clause, where an index would say only that two lists happen to
     * be in step.
     *
     * <p>A clause this reading did not reach is not here. Nothing of it was proved equal to a
     * constraint, so it is checked as its own condition — which holds a value to the whole rule
     * whatever is missing here, since the rules themselves come from the settled form.
     */
    public static Map<Clause.Id, BoundaryCheck> of(Symbols symbols, TypeSymbol.AtModule named,
                                                   ValueShape.Field sole,
                                                   ExpandedClauseLookup form,
                                                   InvariantStatements statements) {
        return new BoundaryConstraints(symbols, sole.name()).of(named, sole.type(), form,
                statements);
    }

    private Map<Clause.Id, BoundaryCheck> of(TypeSymbol.AtModule named, Type base,
                                             ExpandedClauseLookup form,
                                             InvariantStatements statements) {
        Map<Clause.Id, BoundaryCheck> out = new LinkedHashMap<>();
        for (TypeOps.Declared declared
                : TypeOps.expandedInvariants(named, symbols, form).reached()) {
            List<BoundaryConstraint> stated = new ArrayList<>();
            boolean checkCondition = false;
            // The parts the clause was split into, with the tree the expansion made of each. Split
            // again here, this would be a second answer to which parts a clause has, taken off a
            // tree an expansion left.
            for (AuthoredShape.Written part : declared.parts()) {
                List<BoundaryConstraint> states = constraintsOf(part.id(), base, statements);
                if (states == null) {
                    checkCondition = true;
                } else {
                    stated.addAll(states);
                }
            }
            // A spread reached twice reaches one clause twice, and both readings are of it.
            out.merge(new Clause.Id(declared.declaredOn(), declared.ordinal()),
                    new BoundaryCheck(stated, checkCondition), (was, now) -> {
                        if (!was.equals(now)) {
                            throw new IllegalStateException("one clause of " + named
                                    + " read as two boundary checks: " + was + " and " + now);
                        }
                        return was;
                    });
        }
        return out;
    }

    /**
     * The constraints one part states, or null where it keeps its own check.
     *
     * <p><b>Recognised statement by statement and committed part by part.</b> A part states as many
     * rules as the reading arrives at — a denied choice states one per branch — and each of them is
     * mapped on its own. What is stated is all of them or none: a part half of whose rules became
     * constraints would report one of its own statements as a constraint and the other as the
     * clause, so one thing an author wrote would break in two different words depending on which
     * half the value broke.
     *
     * <p>Null where the reading has no form for the clause, which is not a part that constrains
     * nothing: the rule still runs, and what it reaches the boundary as is its own condition.
     */
    private List<BoundaryConstraint> constraintsOf(PartId<RuleRef.Invariant> part, Type base,
                                                   InvariantStatements statements) {
        List<InvariantStatement> states = statements.of(part);
        if (states == null) {
            return null;
        }
        List<BoundaryConstraint> out = new ArrayList<>();
        for (InvariantStatement each : states) {
            Optional<BoundaryConstraint> c = of(each, base);
            if (c.isEmpty()) {
                return null;
            }
            out.add(c.get());
        }
        return List.copyOf(out);
    }

    /**
     * What one side of a comparison is of the value a constraint would be about, or null where it is
     * about something else.
     *
     * <p>Which side that is, is the reading's to spend ({@link StatedComparison#at}), so this says
     * only what a side is and never which of them bore it.
     */
    private enum Measured {

        /** The value itself. */
        VALUE,
        /** How many characters it has. */
        STRING_LENGTH,
        /** How many elements it has. */
        LIST_LENGTH,
        /** How many entries it has. */
        MAP_SIZE
    }

    /**
     * The constraint equivalent to {@code statement} on a field whose value is a {@code base}, or
     * empty when this cannot prove one.
     */
    private Optional<BoundaryConstraint> of(InvariantStatement statement, Type base) {
        return switch (statement) {
            case InvariantStatement.Unread _ -> Optional.empty();
            case InvariantStatement.Applies it -> ofCall(it.call(), base);
            case InvariantStatement.Compares it -> ofComparison(it.states(), base);
        };
    }

    private Optional<BoundaryConstraint> ofComparison(StatedComparison states, Type base) {
        // `0 <= value` says what `value >= 0` says, and which side bore the value is spent here:
        // what comes back is a claim about the value and what it is held against, in that order.
        StatedComparison.Numbered<Measured> bound = states.at(this::measured);
        if (bound == null) {
            return Optional.empty();
        }
        ComparisonClaim placed = bound.claim();
        Core against = bound.other();
        if (base == Type.STRING) {
            return bound.number() == Measured.STRING_LENGTH
                    ? ofStringLength(placed, against) : Optional.empty();
        }
        if (base == Type.INT) {
            return bound.number() == Measured.VALUE ? ofInt(placed, against) : Optional.empty();
        }
        if (base == Type.DECIMAL) {
            return bound.number() == Measured.VALUE ? ofDecimal(placed, against) : Optional.empty();
        }
        if (base instanceof Type.ListOf) {
            return bound.number() == Measured.LIST_LENGTH
                    ? ofListSize(placed, against) : Optional.empty();
        }
        if (base instanceof Type.MapOf) {
            return bound.number() == Measured.MAP_SIZE
                    ? ofMapSize(placed, against) : Optional.empty();
        }
        return Optional.empty();
    }

    /** What {@code e} is of the field's value, or null where it is about something else. */
    private Measured measured(Core e) {
        if (isValue(e)) {
            return Measured.VALUE;
        }
        if (!(Core.withoutStanding(e) instanceof Core.PreservedCall call) || call.args().size() != 1
                || !isValue(call.args().get(0))) {
            return null;
        }
        if (applies(call, Kernel.STRING_LENGTH)) {
            return Measured.STRING_LENGTH;
        }
        if (applies(call, Kernel.LIST_LENGTH)) {
            return Measured.LIST_LENGTH;
        }
        return applies(call, Kernel.MAP_SIZE) ? Measured.MAP_SIZE : null;
    }

    /**
     * The bound at {@code end} that admits what a bound placed at {@code n} admits, or null where
     * there is none to name.
     *
     * <p>A length, a size and an {@code Int} are whole numbers, so a bound that refuses the number
     * it names admits exactly what the next one along admits — and the constraints are inclusive,
     * so that is the one to state. At either end of what the constraint can hold there is no next
     * number, and the clause keeps the check it already has.
     */
    private static Long inclusiveAt(EndSide end, boolean holdsAtTheValue, long n,
                                    long least, long most) {
        if (holdsAtTheValue) {
            return n;
        }
        if (end == EndSide.LOWER) {
            return n == most ? null : n + 1;
        }
        return n == least ? null : n - 1;
    }

    /** Which end of the values a comparison bounds: the side it is satisfied on is where its
     *  values run from. */
    private static EndSide endOf(ComparisonClaim.Cut cut) {
        return EndSide.facing(cut.satisfyingSide());
    }

    /**
     * A bound on how many elements a list has: {@code List.length(value) >= 1} is non-emptiness,
     * {@code >= 3} a minimum of three, and so on. A size is a whole number, so a strict bound is the
     * adjacent inclusive one — read the same way a string's length is.
     *
     * <p>A {@code Set} has no entry of its own here. Souther decodes one as a list and drops the
     * duplicates while mapping it (spec §collections), so a constraint on the decoded list would
     * count the duplicates the set does not have.
     */
    private static Optional<BoundaryConstraint> ofListSize(ComparisonClaim placed, Core against) {
        Integer n = sizeBound(against);
        if (n == null) {
            return Optional.empty();
        }
        return switch (placed) {
            case ComparisonClaim.Singled singled ->
                    singled.holdsAtTheValue() ? Optional.of(new FixedSize(n)) : Optional.empty();
            case ComparisonClaim.Cut cut -> {
                EndSide end = endOf(cut);
                Long at = inclusiveAt(end, cut.holdsAtTheValue(), n, 0, Integer.MAX_VALUE);
                yield at == null ? Optional.empty()
                        : Optional.of(end == EndSide.LOWER
                                ? at == 1 ? new NonEmpty() : new MinSize(at.intValue())
                                : new MaxSize(at.intValue()));
            }
        };
    }

    /** The same for a map, bounded by entry count. {@code >= 1} is a minimum of one entry. */
    private static Optional<BoundaryConstraint> ofMapSize(ComparisonClaim placed, Core against) {
        Integer n = sizeBound(against);
        if (n == null || !(placed instanceof ComparisonClaim.Cut cut)) {
            return Optional.empty();
        }
        EndSide end = endOf(cut);
        Long at = inclusiveAt(end, cut.holdsAtTheValue(), n, 0, Integer.MAX_VALUE);
        return at == null ? Optional.empty()
                : Optional.of(end == EndSide.LOWER
                        ? new MapMinSize(at.intValue()) : new MapMaxSize(at.intValue()));
    }

    /** The literal bound a size is held against, or null when it is held against something else. */
    private static Integer sizeBound(Core against) {
        Long bound = intLiteral(against);
        if (bound == null || bound < 0 || bound > Integer.MAX_VALUE) {
            return null;
        }
        return bound.intValue();
    }

    private Optional<BoundaryConstraint> ofCall(Core.PreservedCall call, Type base) {
        // What the pattern means, as the checker settled it on the call, and the text the call was
        // given: this reads no pattern text.
        if (base == Type.STRING && applies(call, Kernel.STRING_MATCHES) && call.args().size() == 2
                && isValue(call.args().get(1))) {
            return Optional.of(matching(call));
        }
        // `List.allDistinctBy(x -> x, value)` says of the elements that no two are equal, by the same
        // value equality (spec §collections). A projection that is not the identity says it
        // of something else — the elements' products, their ids — and there is no constraint for
        // that, so the clause keeps its own check.
        if (base instanceof Type.ListOf && statesDistinctness(call)
                && call.args().size() == 2 && isValue(call.args().get(1))
                && isIdentity(call.args().get(0))) {
            return Optional.of(new Unique());
        }
        return Optional.empty();
    }

    private static Optional<BoundaryConstraint> ofStringLength(ComparisonClaim placed,
                                                               Core against) {
        Integer bound = sizeBound(against);
        if (bound == null) {
            return Optional.empty();
        }
        int n = bound;
        return switch (placed) {
            case ComparisonClaim.Singled singled ->
                    singled.holdsAtTheValue() ? Optional.of(new FixedLength(n)) : Optional.empty();
            case ComparisonClaim.Cut cut -> {
                EndSide end = endOf(cut);
                Long at = inclusiveAt(end, cut.holdsAtTheValue(), n, 0, Integer.MAX_VALUE);
                yield at == null ? Optional.empty()
                        : Optional.of(end == EndSide.LOWER
                                ? new MinLength(at.intValue()) : new MaxLength(at.intValue()));
            }
        };
    }

    private static Optional<BoundaryConstraint> ofInt(ComparisonClaim placed, Core against) {
        Long bound = intLiteral(against);
        if (bound == null || !(placed instanceof ComparisonClaim.Cut cut)) {
            return Optional.empty();
        }
        long n = bound;
        EndSide end = endOf(cut);
        // A bound at nought is stated as the sign it is, and the two of them as two: a bound
        // refusing nought is `Positive` where the same bound moved to one is a minimum of one. So
        // which of them a rule comes to is read before the bound is moved — unlike a list, where the
        // bound at one and the bound past nought are the one constraint and moving first says so.
        if (end == EndSide.LOWER && n == 0) {
            return Optional.of(cut.holdsAtTheValue() ? new NonNegative() : new Positive());
        }
        Long at = inclusiveAt(end, cut.holdsAtTheValue(), n, Long.MIN_VALUE, Long.MAX_VALUE);
        return at == null ? Optional.empty()
                : Optional.of(end == EndSide.LOWER ? new Min(at) : new Max(at));
    }

    private static Optional<BoundaryConstraint> ofDecimal(ComparisonClaim placed, Core against) {
        BigDecimal bound = decimalLiteral(against);
        if (bound == null || !(placed instanceof ComparisonClaim.Cut cut)) {
            return Optional.empty();
        }
        boolean zero = bound.signum() == 0;
        // A Decimal has no next value, so a bound refusing the number it names is no inclusive
        // bound at all — except at nought, which is stated as the sign it is.
        if (!cut.holdsAtTheValue()) {
            return endOf(cut) == EndSide.LOWER && zero
                    ? Optional.of(new DecimalPositive()) : Optional.empty();
        }
        return Optional.of(endOf(cut) == EndSide.LOWER
                ? zero ? new DecimalNonNegative() : new DecimalMin(bound)
                : new DecimalMax(bound));
    }

    /** Whether {@code e} reads the data's one field. */
    private boolean isValue(Core e) {
        return Core.withoutStanding(e) instanceof Core.Read read && read.name().equals(field);
    }

    /** The constraint for the pattern the checker settled on {@code call}. A kept
     *  {@code String.matches} exists only where its pattern was read, so a call without one is the
     *  checker's contract broken. */
    private static Pattern matching(Core.PreservedCall call) {
        if (!(call.settled() instanceof Core.KernelFact.StringMatches settled)) {
            throw new IllegalStateException(
                    "a String.matches call carries the pattern the checker read: " + call);
        }
        return new Pattern(settled.meaning(), settled.written());
    }

    /**
     * Whether {@code call} applies {@code kernel} — asked of what the name reaches, which is what a
     * library operation is filed under whether or not an import let it be written bare, and then of
     * which kernel the library declares that operation to be.
     *
     * <p>The kernel and not the alias. What makes a length comparison a size constraint is that the
     * call computes a length; the alias it is published under is the library's, and a clause
     * recognised by one would go on being recognised for exactly as long as the two agreed.
     *
     * <p>A call applying a name nothing declares, or one that is no kernel, applies no operation
     * this recognises. There is no constraint to map it to, and the clause keeps the check it
     * already has.
     */
    private boolean applies(Core.PreservedCall call, Kernel kernel) {
        return call.operation() instanceof ValueName.Stdlib.Operation operation
                && symbols.kernelOf(operation) == kernel;
    }

    /** Whether {@code call} states that the elements are distinct — the library's own predicate for
     *  it, which has a Souther body rather than a kernel and so is a value the library hands over
     *  ({@link Symbols#theDistinctnessPredicate}). */
    private boolean statesDistinctness(Core.PreservedCall call) {
        return symbols.theDistinctnessPredicate().equals(call.operation());
    }

    /** Whether a projection hands back what it was given — {@code x -> x}, however the parameter is
     * spelled. A block with one parameter is how a lambda arrives here (spec §blocks). The body reads
     * the parameter when it reads that binding; a name spelled like it, bound elsewhere, is another
     * value. */
    private static boolean isIdentity(Core e) {
        return Core.withoutStanding(e) instanceof Core.Block block && block.params().size() == 1
                && Core.withoutStanding(block.body()) instanceof Core.Read read
                && read.binding().equals(block.params().get(0).binding());
    }

    /** An Int literal, negation included ({@code -1}), or null when the operand is not one. */
    private static Long intLiteral(Core standing) {
        Core e = Core.withoutStanding(standing);
        if (e instanceof Core.Int lit) {
            return lit.value();
        }
        if (e instanceof Core.Neg neg && Core.withoutStanding(neg.operand()) instanceof Core.Int lit
                && IntNegation.hasValue(lit.value())) {
            return -lit.value();
        }
        return null;
    }

    /** A Decimal literal; an Int literal counts, since a bare literal takes the other side's type. */
    private static BigDecimal decimalLiteral(Core standing) {
        Core e = Core.withoutStanding(standing);
        if (e instanceof Core.Decimal lit) {
            return lit.value();
        }
        if (e instanceof Core.Neg neg
                && Core.withoutStanding(neg.operand()) instanceof Core.Decimal lit) {
            return lit.value().negate();
        }
        Long asInt = intLiteral(e);
        return asInt == null ? null : BigDecimal.valueOf(asInt);
    }
}
