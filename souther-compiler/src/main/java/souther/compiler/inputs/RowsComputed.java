package souther.compiler.inputs;

import souther.compiler.inputs.WhatARelationLeavesUndivided.Operations;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Term;
import souther.compiler.numeric.ExactRatio;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;

/**
 * Whether the rows of a relation are computed, asked in one place.
 *
 * <p>A row is computed where the program that holds the relation gets to the end of working it
 * out, and the relation says only the form: the terms weighed, and a constant. What the program
 * does beyond that is what a reading of the comparison told ({@link Operations}), in one of three
 * states, and every question here is answered by the state and by nothing else.
 *
 * <ul>
 * <li>{@link WhatARelationLeavesUndivided.Told#EVERY}: every operation that can stop a run is
 * told, so a row is computed where each of them holds at it, in the program's own order and signs,
 * and the sizes of the form's addends say nothing of it.
 * <li>{@link WhatARelationLeavesUndivided.Told#SOME}: the reading met something that can stop a
 * run and told of no operation for it. The told operations still say where a row cannot be; no
 * row is shown computed, because what is not told may stop it.
 * <li>{@link WhatARelationLeavesUndivided.Told#NOTHING_SAID}: no reading of the program was made
 * (a product, a whole and its part, a difference, a relation derived from a comparison), and the
 * caller takes the program to add the form up and nothing else. Then the sizes of the addends say
 * it: a row adding up addends whose positive ones together and negative ones together are no
 * further from nought than the greatest value is computed in whatever order and with whichever
 * sign, since every sum along the way lies between the two and so does the sum turned round.
 * </ul>
 *
 * <p>The sizes are never asked of a program that is read: {@code a + 3 >= b} stops at an
 * {@code a} whose addends are small. They are asked of the form only through
 * {@link #computesAsTheFormIsAdded}, whose name is the assumption, and which answers nothing for
 * a program that was read.
 *
 * @param greatest   the greatest value of the type, or null where it has none
 * @param operations what the rows of the relation work out
 * @param held       the terms a row is asked of two others while they stand still, each at the
 *                   value it is held at, by its key ({@link Term#key}); none where the row names
 *                   every term
 */
record RowsComputed(BigInteger greatest, Operations operations, Map<Object, ExactRatio> held) {

    /** A type with no greatest value: every row is computed. */
    static final RowsComputed ENDLESS = new RowsComputed(null, Operations.NONE, Map.of());

    RowsComputed {
        held = Map.copyOf(held);
    }

    static RowsComputed upTo(BigInteger greatest) {
        return greatest == null ? ENDLESS : new RowsComputed(greatest, Operations.NONE, Map.of());
    }

    /** The same, over a relation whose rows work out {@code operations}. */
    RowsComputed withOperations(Operations operations) {
        return new RowsComputed(greatest, operations, held);
    }

    /** The same, for rows in which the terms called by the keys of {@code standing} stand at
     *  their values, which a row of the two others does not name. */
    RowsComputed withTheRestAt(Map<Object, ExactRatio> standing) {
        Map<Object, ExactRatio> together = new LinkedHashMap<>(held);
        together.putAll(standing);
        return new RowsComputed(greatest, operations, together);
    }

    /** Whether it stops at a size, so that a row can fail to be computed. */
    boolean stopsAtASize() {
        return greatest != null;
    }

    /** Whether every operation that can stop a run is told. */
    boolean tellsEveryOperation() {
        return operations.told() == WhatARelationLeavesUndivided.Told.EVERY;
    }

    /**
     * Whether no row can fail to be computed: the type holds no greatest value, and nothing the
     * program does can stop a row either. A type with no greatest value says only that no size
     * stops a run; a number built into a type with an invariant, or an operation told, still can.
     */
    boolean nothingStopsARow() {
        return greatest == null && !mayStopARow();
    }

    /** Whether the rows of the relation work out an operation of decimals. */
    boolean worksOutDecimals() {
        return !operations.decimals().isEmpty();
    }

    /**
     * Whether what rows built at the ends of a run find of the operations of decimals told holds
     * of every number between, for a claim about the values of the term {@code asked} with the
     * term {@code partner} put where it takes the claim ({@link DecimalOperation#allowAClaimOver}).
     * True where there is none.
     */
    boolean decimalsAllowAClaimOver(Object asked, Object partner) {
        return DecimalOperation.allowAClaimOver(operations.decimals(), asked, partner);
    }

    /**
     * Whether a run of the term {@code asked} with no end on a side is asked at the edge of what
     * is built ({@link DecimalPoints#edgeOfWhatIsBuilt}) and the rows there stand for the numbers
     * between: every operation that can stop a row is an operation of decimals, and none of them
     * reads the term, so the room of one turns on the scales of the numbers a row is built from
     * and not on which number of the run is asked of.
     *
     * <p>The numbers a row is built from are written at most as many places before and after the
     * point as {@link DecimalOperation#PLACES_A_ROW_IS_BUILT_AT}, and the partner is stood beside
     * the line at such numbers however far out the line is, so two operands of a sum are at most
     * twice that many places apart in scale whatever the digits. The room of the operations is
     * then the same at every number of the run, and the point far out is asked as any end is,
     * to see that the term takes a value there and the rows stand. That a term put beside it
     * reaches the line at every number is {@code reaches}' own question, asked before the rows
     * are.
     */
    boolean aRunWithNoEndIsAskedAtTheEdgeOfWhatIsBuilt(Object asked) {
        return greatest == null && tellsEveryOperation() && operations.sums().isEmpty()
                && worksOutDecimals()
                && DecimalOperation.readsOf(operations.decimals()).stream()
                        .noneMatch(reads -> reads.contains(asked));
    }

    /**
     * Whether one row is computed, the row being the {@code addends} of the form at it and the
     * {@code values} of the terms by key.
     */
    boolean rowIsComputed(Supplier<ExactRatio[]> addends,
                          Supplier<Map<Object, ExactRatio>> values) {
        return switch (operations.told()) {
            case EVERY -> computedAt(values);
            case SOME -> false;
            case NOTHING_SAID -> computes(addends.get());
        };
    }

    /**
     * Whether every operation told holds at a row whose terms stand at {@code values}, each by its
     * key, and the rest at where they are held; false where the operations are not all told, or
     * where one of them reads a term neither names.
     */
    boolean computedAt(Supplier<Map<Object, ExactRatio>> values) {
        if (!tellsEveryOperation()) {
            return false;
        }
        Map<Object, ExactRatio> standing = new LinkedHashMap<>(held);
        standing.putAll(values.get());
        return operations.sums().stream().allMatch(sum -> sum.holdsAt(standing))
                && DecimalOperation.allCompleteAt(operations.decimals(), standing);
    }

    /**
     * Whether rows of the farthest {@code sizes} are computed: where every operation is told, if
     * each is a multiple of a sum of the form ({@link Operations#multipleOfTheForm}) and the
     * sizes taken that many times keep inside the type, since such a sum lies between the
     * positive addends and the negative ones together.
     */
    <P> boolean farthestRowsAreComputed(List<Term<P>> terms, ExactRatio constant,
                                        ExactRatio... sizes) {
        return switch (operations.told()) {
            case SOME -> false;
            case NOTHING_SAID -> computes(sizes);
            case EVERY -> {
                ExactRatio multiple = operations.multipleOfTheForm(terms, constant);
                yield multiple != null && computes(timesEach(sizes, multiple));
            }
        };
    }

    /**
     * Whether the sizes of the form's addends may be let go of, to ask whether the relation holds
     * in one row and fails in another: true where the program is taken to add the form, or every
     * operation told is a multiple of a sum of it, and never where something untold may stop a
     * row.
     */
    <P> boolean theSizesMayBeLetGo(List<Term<P>> terms, ExactRatio constant) {
        return switch (operations.told()) {
            case NOTHING_SAID -> true;
            case SOME -> false;
            case EVERY -> operations.multipleOfTheForm(terms, constant) != null;
        };
    }

    /**
     * Whether a relation of two terms compared with each other and nothing added is computed
     * whatever the terms are: true only where nothing can stop a run — no operation is told
     * where every one is, or the program is taken to add the form.
     */
    boolean mayStopARow() {
        return operations.canStopARow();
    }

    /**
     * Whether a row adding up {@code addends} is computed, for a program taken to add the form
     * up and nothing else. For a program a reading was made of, nothing is answered: the sizes
     * are not what stops it.
     */
    boolean computesAsTheFormIsAdded(ExactRatio... addends) {
        return operations.told() == WhatARelationLeavesUndivided.Told.NOTHING_SAID
                && computes(addends);
    }

    private static ExactRatio[] timesEach(ExactRatio[] sizes, ExactRatio multiple) {
        ExactRatio[] over = new ExactRatio[sizes.length];
        for (int i = 0; i < sizes.length; i++) {
            over[i] = sizes[i] == null ? null : sizes[i].times(multiple).orNull();
        }
        return over;
    }

    /** Whether the positive addends together and the negative ones together are within the
     *  greatest; an addend that is no number is no row. */
    private boolean computes(ExactRatio... addends) {
        for (ExactRatio each : addends) {
            if (each == null) {
                return false;
            }
        }
        if (greatest == null) {
            return true;
        }
        ExactRatio up = ExactRatio.ZERO;
        ExactRatio down = ExactRatio.ZERO;
        for (ExactRatio each : addends) {
            if (up == null || down == null) {
                return false;
            }
            if (each.signum() > 0) {
                up = up.plus(each).orNull();
            } else {
                down = down.plus(each).orNull();
            }
        }
        return up != null && down != null && up.compareTo(ExactRatio.of(greatest)) <= 0
                && down.negated().compareTo(ExactRatio.of(greatest)) <= 0;
    }
}
