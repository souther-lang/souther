package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.Extreme;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.ElementKey;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.InputNumber;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.ObservationSource;
import souther.compiler.inputs.PlacesMoved;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.TraversalDirection;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;
import souther.test.ClosedWorldContract;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A number moved by a move that leaves every place it is read off where it stands is that number:
 * of every kind of number, and over every kind of run.
 *
 * <p>Which is what lets the places a number is read off be the places a move is handed
 * ({@link NumericTerm#placesReadOff}): asked as a move that moves nothing, a number answering
 * that it is no number there is a number read off nothing, apart from every other. A number that
 * cannot be moved anywhere else — a selection names places of the input it was read in, a run
 * whose order was shown where it stands — is still the number it is where it stands.
 *
 * <p>Over the kinds and not over a list of them: a kind of number or of run added is one this
 * holds to the same, and fails until it has a number here.
 */
@ClosedWorldContract
class ANumberMovedWhereItStandsIsTheNumberItIsTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());
    private static final TermPath XS = TermPath.of("xs");
    private static final TermPath ELEMENT = XS.element();
    private static final TermPath LINES = TermPath.of("orders").element().then("lines");
    private static final TermPath LINE = LINES.element();
    private static final ElementProjection ITSELF = ElementProjection.ofFields(List.of());
    private static final ElementProjection KEY = ElementProjection.ofFields(List.of("k"));
    private static final ElementProjection N = ElementProjection.ofFields(List.of("n"));

    private static final Proposition FLAGGED =
            new Proposition.Present(new DecisionSubject.AnInput(LINE.then("n")), true);
    private static final KeptOccurrences KEPT = new KeptOccurrences(
            new DecisionSubject.AnInput(LINES), FLAGGED,
            AStatementAtARow.of(FLAGGED, "f", null));

    private static NumericTerm.TakenOver totalOver(RunSource run) {
        return NumericTerm.TakenOver.of(ValueName.Stdlib.operation("List", "sum"), run,
                Type.Prim.INT, NewtypeInners.NONE, SYMBOLS);
    }

    /** One run of each kind. */
    private static List<RunSource> runs() {
        ElementValue byPosition = new ElementValue.ByPosition(
                new ElementValue.PositionTest(2, Rel.EQ, 0),
                new ElementValue.Affine(LinearForm.atom(ITSELF)),
                new ElementValue.Affine(new LinearForm<>(ExactRatio.ZERO,
                        Map.of(ITSELF, ExactRatio.of(3)))));
        return List.of(
                RunSource.overTheOccurrencesAt(ELEMENT),
                new RunSource.FlattenedOccurrences(LINE),
                RunSource.computedOverTheElementsAt(ELEMENT,
                        new ElementValue.Affine(LinearForm.atom(N)), Type.Prim.INT, null),
                ((NumericTerm.TakenOver) InputNumber.overWhatWasComputedByPosition(
                        ValueName.Stdlib.operation("List", "sum"), XS, byPosition,
                        Type.Prim.INT, TraversalDirection.FORWARD, NewtypeInners.NONE, SYMBOLS))
                        .source(),
                new RunSource.JoinedOccurrences(ELEMENT, TermPath.of("ys").element()),
                RunSource.overTheNodesBelow(TermPath.of("n"), List.of("kids"),
                        List.of("xs")));
    }

    /** At least one number of each kind, a selection and a key chosen by case among them. */
    private static List<NumericTerm> numbers() {
        CasesLeft a = CasesLeft.of(Refinement.of(new Case.SumCase(
                TypeSymbols.declared(new TypeKey("probe", "A")), true)));
        CasesLeft b = CasesLeft.of(Refinement.of(new Case.SumCase(
                TypeSymbols.declared(new TypeKey("probe", "B")), true)));
        ElementKey byCase = new ElementKey.ByCase(ITSELF, List.of(
                new ElementKey.ByCase.Arm(a, ITSELF.narrowedTo(a).then("k")),
                new ElementKey.ByCase.Arm(b, ITSELF.narrowedTo(b).then("k"))));
        ElementValue n = new ElementValue.Affine(LinearForm.atom(N));
        List<NumericTerm> out = new ArrayList<>(Arrays.asList(
                new NumericTerm.ValueOf(TermPath.of("x")),
                NumericTerm.TakenOf.of(ValueName.Stdlib.operation("String", "length"),
                        ObservationSource.asItStands(TermPath.of("s")), TakenArguments.NONE,
                        Type.STRING, NewtypeInners.NONE, SYMBOLS),
                NumericTerm.CodePointClassCount.of(TermPath.of("s"),
                        new CodePointClass.NotWhitespace(), CaseMapping.NONE, Type.STRING,
                        NewtypeInners.NONE),
                NumericTerm.CodePointValueSum.of(TermPath.of("s"), Type.STRING,
                        NewtypeInners.NONE),
                NumericTerm.CodePointAt.of(TermPath.of("s"), 3, Type.STRING, NewtypeInners.NONE),
                NumericTerm.WholeUnitsOf.of(ValueName.Stdlib.operation("DateTime", "toDate"),
                        TermPath.of("t"), Type.Prim.DATETIME, NewtypeInners.NONE,
                        ScopedDeclarations.accessOf(SYMBOLS)),
                NumericTerm.Multiplicity.of(XS, ELEMENT.then("k")),
                NumericTerm.ExtremeOfItsKey.of(XS, ELEMENT.then("k"), ELEMENT.then("n"),
                        Extreme.LEAST),
                NumericTerm.OccurrencesOfItsValue.of(new RunSource.FlattenedOccurrences(LINE)),
                NumericTerm.OccurrencesOfItsValue.of(RunSource.overTheOccurrencesAt(ELEMENT),
                        null),
                NumericTerm.OccurrencesOfItsValue.of(new RunSource.FlattenedOccurrences(LINE),
                        KEPT),
                NumericTerm.OccurrencesOfAKey.of(new RunSource.FlattenedOccurrences(LINE),
                        TermPath.of("k")),
                NumericTerm.GatheredUnderItsKey.of(ELEMENT, new ElementKey.At(KEY), n,
                        Type.Prim.INT, NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, null),
                NumericTerm.GatheredUnderItsKey.of(LINE, new ElementKey.At(KEY), n,
                        Type.Prim.INT, NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, KEPT),
                NumericTerm.GatheredUnderItsKey.of(ELEMENT, byCase, n, Type.Prim.INT,
                        NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, null),
                NumericTerm.GatheredUnderAKey.of(ELEMENT, new ElementKey.At(KEY), n,
                        Type.Prim.INT, NumericTerm.GatheredUnderItsKey.Gathering.TOTAL,
                        TermPath.of("k"))));
        runs().forEach(run -> out.add(totalOver(run)));
        return out;
    }

    @Test
    void everyKindOfNumberAndOfRunHasANumberHere() {
        List<NumericTerm> numbers = numbers();
        assertFalse(numbers.stream().anyMatch(Objects::isNull),
                () -> "every fixture is a number: " + numbers);
        Set<Class<?>> held = new LinkedHashSet<>();
        numbers.forEach(each -> held.add(each.getClass()));
        assertEquals(kindsOf(NumericTerm.class), held);
        Set<Class<?>> run = new LinkedHashSet<>();
        runs().forEach(each -> run.add(each.getClass()));
        assertEquals(kindsOf(RunSource.class), run);
    }

    @Test
    void aNumberMovedWhereItStandsIsTheNumberItIs() {
        for (NumericTerm number : numbers()) {
            assertEquals(number, number.movedTo(PlacesMoved.nowhere()), number::toString);
            assertFalse(number.placesReadOff().isEmpty(), number::toString);
        }
    }

    /** The classes a sealed type comes to, through every sealed type between. */
    private static Set<Class<?>> kindsOf(Class<?> sealed) {
        Set<Class<?>> out = new LinkedHashSet<>();
        for (Class<?> each : sealed.getPermittedSubclasses()) {
            if (each.isSealed()) {
                out.addAll(kindsOf(each));
            } else {
                out.add(each);
            }
        }
        return out;
    }
}
