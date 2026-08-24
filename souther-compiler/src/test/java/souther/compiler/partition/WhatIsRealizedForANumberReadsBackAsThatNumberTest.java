package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.NumericAnswers;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Reading a number off a row and writing a value that answers it are the two directions of one
 * account, and this is what holds them to each other.
 *
 * <p><b>Not that they are inverse.</b> Neither direction is injective: many strings are five long,
 * and {@code Int.abs} answers three at three and at minus three. So what is asked is one way round —
 * every value built for a number reads back as that number. The other way round is not asked and
 * would be wrong to: which of the values answering a number a realizer offers is its business, and
 * an operation whose values are chosen from a wide set would fail a test that demanded the one it
 * started from.
 *
 * <p>Asked over the declarations rather than over a list written here. Every operation that declares
 * what it takes of the one value it is given is walked, so an operation declared tomorrow is inside
 * this without a line being added — which is the whole point of the answers having moved onto the
 * operation (#1027).
 */
class WhatIsRealizedForANumberReadsBackAsThatNumberTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());
    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12);
    private static final TermPath AT = TermPath.of("x");

    /**
     * Numbers the operation actually answers, which is where its own bound runs.
     *
     * <p>Asked of the operation rather than written here. An hour of the day stops at twenty-three
     * and a count does not stop at all, and a walk over numbers of its own would be testing one of
     * them outside what it answers — where building nothing is the right answer and reading nothing
     * back proves nothing.
     */
    private static List<Long> answerable(NumericTerm term) {
        List<Long> out = new ArrayList<>();
        for (long each : new long[] {0, 1, 3, 7, 23}) {
            if (term.intrinsicBounds().admits(Count.of(each))) {
                out.add(each);
            }
        }
        return out;
    }

    /** The type each operation is applied to, for the walk below to have a position to stand at. */
    private static Type sourceOf(ValueName operation) {
        Type declared = DefaultStdlib.get().entry(
                ((ValueName.Stdlib) operation).qualified()).signature().params().get(0);
        // A signature over a type variable is a signature over anything, and a walk needs one thing.
        // `Int` is the element every collection below is asked to hold, so what is built is a value
        // of a type the language certainly has.
        return switch (declared) {
            case Type.ListOf _ -> new Type.ListOf(Type.INT);
            case Type.SetOf _ -> new Type.SetOf(Type.INT);
            case Type.MapOf _ -> new Type.MapOf(Type.INT, Type.INT);
            default -> declared;
        };
    }

    /**
     * Every account of what an operation takes is one some operation declares.
     *
     * <p>The runtime half of a compile-time closure. That an account added is one the reader and the
     * realizer cannot compile without is the switches' to say, and Java says it at build time; what
     * it cannot say is that the account was ever declared of anything, and an account nothing
     * declares is an arm nothing below would exercise.
     */
    @Test
    void everyAccountOfWhatIsTakenIsDeclaredOfSomeOperation() {
        List<Class<?>> arms = List.of(TakenAs.class.getPermittedSubclasses());
        assertFalse(arms.isEmpty(), "the accounts are a sealed set and there is at least one");
        for (Class<?> arm : arms) {
            assertTrue(OperationFacts.answersANumberTakenOfItsArgument().stream()
                            .anyMatch(each -> arm.isInstance(OperationFacts.takenAs(each))),
                    arm.getSimpleName() + " is an account no operation is declared under, so"
                            + " nothing reads or writes it");
        }
    }

    /**
     * What is built for a number reads back as that number, for every operation there is.
     *
     * <p>Over the numbers a caller of either direction actually holds: nought, because an empty
     * value is a value like any other and a magnitude of nought is one number rather than two, and
     * upwards from there. A count below nought is not a number any of these answers and is asked of
     * neither direction here.
     */
    @Test
    void everyValueBuiltForANumberReadsBackAsIt() {
        int checked = 0;
        for (ValueName operation : OperationFacts.answersANumberTakenOfItsArgument()) {
            NumericTerm.TakenOf term =
                    new NumericTerm.TakenOf((ValueName.Stdlib) operation, AT);
            Type source = sourceOf(operation);
            Carrier answered = term.answeredOn(source, SYMBOLS);
            Carrier observed = term.observedOn(source, SYMBOLS);
            assertNotNull(answered, operation + " answers a number, so there is an order for it");
            for (long each : answerable(term)) {
                Place asked = Count.of(each);
                TermRealizations.Realization made =
                        TermRealizations.at(term, source, answered, asked, SYMBOLS, POLICY);
                // An operation that builds nothing at a number is not a failure of this: whether
                // anything answers it is `EveryAnswerItCanGiveHasASourceValue`, asked below.
                if (!(made instanceof TermRealizations.Realization.Built built)) {
                    continue;
                }
                for (FixtureTemplate value : built.values()) {
                    assertEquals(new NumericTerm.Reading.Number(asked),
                            term.read(observed(value), observed),
                            operation + " built " + value.text() + " for " + each
                                    + ", and it does not read back as that");
                    checked++;
                }
            }
        }
        // So that a walk which built nothing anywhere cannot pass as a walk that found nothing
        // wrong. What the number is does not matter and is not asserted; that there was one does.
        assertTrue(checked > 0, "nothing was built, so nothing was read back");
    }

    /**
     * And where the operation says every number it answers is one some value answers, something is
     * built for each of them.
     *
     * <p>Beside the reading above and not folded into it. That what was built reads back is one
     * statement and that anything is built is another: an operation counting things the language may
     * have none of satisfies the first at every number and the second at none, which is why the
     * second is a fact about the operation rather than something a realizer is trusted for.
     */
    @Test
    void everyNumberAnOperationSaysHasAValueIsOneSomethingIsBuiltFor() {
        for (ValueName operation : OperationFacts.answersANumberTakenOfItsArgument()) {
            if (!OperationFacts.everyAnswerItCanGiveHasASourceValue(operation)) {
                continue;
            }
            NumericTerm.TakenOf term =
                    new NumericTerm.TakenOf((ValueName.Stdlib) operation, AT);
            Type source = sourceOf(operation);
            Carrier answered = term.answeredOn(source, SYMBOLS);
            for (long each : answerable(term)) {
                assertInstanceOf(TermRealizations.Realization.Built.class,
                        TermRealizations.at(term, source, answered, Count.of(each), SYMBOLS, POLICY),
                        operation + " says every number it answers is one some value answers, and"
                                + " nothing was built for " + each);
            }
        }
    }

    /**
     * What each account answers, at the values that tell it from a plausible neighbour.
     *
     * <p>The layer the two above cannot reach. A realizer that wrote only ASCII and a reader that
     * counted UTF-16 units agree with each other at every string either of them would offer, so a
     * round trip is green while a boundary drawn on a string outside the basic plane stands one
     * place away from the rule that drew it. The oracle is written here, in the values themselves.
     */
    @Test
    void whatEachAccountAnswersIsWhatTheLibraryAnswers() {
        assertEquals(Count.of(1),
                number(term("String", "length").read(new ObservedValue.Text("😀"),
                        Carrier.TEXT)),
                "a string counts in code points, and one emoji is one of them");
        assertEquals(Count.of(13),
                number(term("Time", "hour").read(
                        new ObservedValue.Temporal("13:45:12"), Carrier.TIME)),
                "a quarter to two in the afternoon falls in the thirteenth hour");
        assertEquals(Count.of(0),
                number(term("Time", "hour").read(
                        new ObservedValue.Temporal("00:45:12"), Carrier.TIME)),
                "and three quarters of an hour past midnight falls in the noughth");
    }

    /**
     * What such a term is measured by is the operation's result and not the position's type.
     *
     * <p>The two abs operations are the whole of this: one argument type each, one arm between them,
     * and two different orders for a boundary to be drawn on. Read off the arm, or off the kind of
     * term, both would be whole numbers and every strict bound on a decimal magnitude would be
     * sharpened onto a count the term never takes.
     */
    @Test
    void whatATakenNumberIsMeasuredByIsTheOperationsResult() {
        assertEquals(Carrier.WHOLE, term("Time", "hour").answeredOn(Type.Prim.TIME, SYMBOLS),
                "an hour is counted by one");
        assertEquals(Carrier.TIME, term("Time", "hour").observedOn(Type.Prim.TIME, SYMBOLS),
                "while the value it is read off counts the seconds of its day");
        assertEquals(Carrier.WHOLE, term("String", "length").answeredOn(Type.STRING, SYMBOLS),
                "and a count is whole however the thing counted is ordered");
        assertEquals(Carrier.TEXT, term("String", "length").observedOn(Type.STRING, SYMBOLS),
                "while what is read at the position is still a string");
    }

    /**
     * A number an operation answers is read off the value's own order, and a boundary on it is drawn
     * on the answer's.
     *
     * <p>The assertion the whole separation turns on, and the one the size operations cannot make:
     * a string has no count of its own, so nothing could tell which of the two orders a single
     * carrier meant. A time has one, and the two orders are different — thirteen hours is
     * forty-six thousand eight hundred seconds — so a reader handed the wrong one answers a number
     * rather than nothing, and nothing about it looks like a failure (#1027).
     */
    @Test
    void theOrderAValueIsReadOnIsNotTheOrderItsAnswerIsMeasuredOn() {
        NumericTerm hour = term("Time", "hour");
        assertEquals(Count.of(13),
                number(hour.read(new ObservedValue.Temporal("13:00:00"), Carrier.TIME)));
        assertInstanceOf(NumericTerm.Reading.NotNumber.class,
                hour.read(new ObservedValue.Temporal("13:00:00"), Carrier.WHOLE),
                "and handed the order the answer is measured on, the same value reads as no number"
                        + " at all — the two orders are not one another's stand-in");
    }

    /**
     * An operation the language gives no account of has no term.
     *
     * <p>Refused where the term is built rather than at whichever reader met it first. Every other
     * answer about such a term comes from the declaration, so one without a declaration is a term
     * read by whatever each reader's default happened to be.
     */
    @Test
    void aTermCannotBeBuiltForAnOperationThatDeclaresNoAccount() {
        assertTrue(OperationFacts.takenAs(ValueName.Stdlib.operation("Date", "year")) == null,
                "the premise: nothing is declared of it yet");
        IllegalArgumentException refused = org.junit.jupiter.api.Assertions.assertThrows(
                IllegalArgumentException.class,
                () -> new NumericTerm.TakenOf(ValueName.Stdlib.operation("Date", "year"), AT));
        assertTrue(refused.getMessage().contains("Date.year"), refused.getMessage());
    }

    /** What the type of the number an operation answers is, asked in the one place that says. */
    @Test
    void theNumberAnOperationAnswersIsTypedByTheLibrary() {
        assertEquals(Type.INT,
                NumericAnswers.typeOf(ValueName.Stdlib.operation("String", "length"), SYMBOLS));
        assertEquals(Type.INT,
                NumericAnswers.typeOf(ValueName.Stdlib.operation("Time", "hour"), SYMBOLS));
        // Not among the terms this change makes, and asked all the same: what an operation answers
        // is a question about the operation, and the answer here is the one that would have been
        // taken from the argument's order by a reader that assembled it itself.
        assertEquals(Type.INT,
                NumericAnswers.typeOf(ValueName.Stdlib.operation("Decimal", "toInt"), SYMBOLS),
                "a decimal rounded to a whole number answers a whole number");
    }

    private static NumericTerm term(String module, String name) {
        return new NumericTerm.TakenOf(ValueName.Stdlib.operation(module, name), AT);
    }

    private static Place number(NumericTerm.Reading read) {
        return assertInstanceOf(NumericTerm.Reading.Number.class, read).value();
    }

    /**
     * A built value as a row holds it.
     *
     * <p>The oracle and not a second decoder. What crosses from a fixture to a row is the run time's
     * to do, and running one to test a boundary would put the whole example pipeline between a
     * question about two functions and its answer. What is written here is the mapping from the
     * literals these realizers actually build, and it is deliberately the simplest reading of them:
     * a test whose oracle repeated the reader's own cleverness would agree with it about being
     * wrong.
     */
    private static ObservedValue observed(FixtureTemplate value) {
        return observed(value.value());
    }

    private static ObservedValue observed(Hir.Expr written) {
        return switch (written) {
            case Hir.IntLit lit -> new ObservedValue.Integer(lit.value());
            case Hir.DecimalLit lit -> new ObservedValue.Decimal(lit.value());
            case Hir.StringLit lit -> new ObservedValue.Text(lit.value());
            case Hir.Neg neg -> negated(observed(neg.operand()));
            case Hir.ListLit list -> collection(list.elements());
            // A temporal is written as the namespace applied to an ISO string, and a row holds it
            // as that text. Which temporal it is the position says, not the text — so the oracle
            // keeps the text and lets the carrier handed to the reader decide, which is the whole
            // arrangement being tested.
            case Hir.Apply built when built.args().size() == 1
                    && built.args().get(0) instanceof Hir.StringLit iso ->
                    new ObservedValue.Temporal(iso.value());
            default -> throw new IllegalStateException(
                    "a realizer built something this oracle does not read: " + written);
        };
    }

    /** A list literal as a row holds it: a sequence, or a mapping where its elements are pairs. */
    private static ObservedValue collection(List<Hir.Expr> elements) {
        List<ObservedValue.Entry> entries = new ArrayList<>();
        for (Hir.Expr each : elements) {
            if (!(each instanceof Hir.Tuple pair) || pair.elements().size() != 2) {
                entries = null;
                break;
            }
            entries.add(new ObservedValue.Entry(observed(pair.elements().get(0)),
                    observed(pair.elements().get(1))));
        }
        if (entries != null && !elements.isEmpty()) {
            return new ObservedValue.Mapping(entries);
        }
        List<ObservedValue> out = new ArrayList<>();
        for (Hir.Expr each : elements) {
            out.add(observed(each));
        }
        return new ObservedValue.Sequence(out);
    }

    private static ObservedValue negated(ObservedValue value) {
        return switch (value) {
            case ObservedValue.Integer whole -> new ObservedValue.Integer(-whole.value());
            case ObservedValue.Decimal dense -> new ObservedValue.Decimal(dense.value().negate());
            default -> throw new IllegalStateException("nothing else is written negated: " + value);
        };
    }
}
