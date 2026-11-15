package souther.compiler.partition;

import souther.compiler.check.Choice;
import souther.compiler.check.DateMonthMoves;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.core.DeclaredOperation;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReads;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.MonthMoveCases;
import souther.compiler.types.ApplicationDerivationCause;
import souther.compiler.types.ApplicationOrigin;
import souther.compiler.types.ReferenceDerivationCause;
import souther.compiler.types.ReferenceOrigin;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.EnumMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * A date moved by months written out, or the day or the year of one, as a call defined in the
 * cases the calendar tells apart ({@link MonthMoveCases}).
 *
 * <p>The cases are stated over numbers of the date the move is made from — its month, what its
 * year leaves by four, one hundred and four hundred, its day — and answer one number as a form of
 * the date's own numbers. Those numbers are written as calls of the library's operations over the
 * date, so a reading of a case reads each as any such call is read, and a call defined by cases
 * is read once for each of them ({@link Pullback.Inside.ACallDefinedByCases}).
 */
final class MonthMovesInCases {

    /**
     * The cases a call is defined in.
     *
     * @param call  the call the cases are of: the move, or the day or the year of it
     * @param move  the operation that moves the date
     * @param cases the cases, in the order they are stated
     */
    record Read(Core call, ValueName.Stdlib move, List<Choice.ADefinitionCase> cases) {}

    private MonthMovesInCases() {
    }

    /**
     * A date that is the first of a month: the first of the month of {@code of}, moved by
     * {@code moved} months.
     *
     * <p>The first of a month moved by months lands on the first of the month it lands in, which
     * is never a day past its end, so what a move of it comes to is stated by the month and year
     * of {@code of} alone, and a move of one is the move by the months of both added.
     *
     * @param of    the date whose month it is the first of, as it is written where it is read
     * @param moved how many months on from the first of the month of {@code of} it is
     */
    record MonthStart(Core of, long moved) {}

    /**
     * The cases {@code e}, read where {@code at} is, is defined in where it is a date moved by
     * months or the day, the month or the year of one — or null where it is neither, or the move
     * is by more months than are read in cases.
     *
     * @param monthStartOf the first of a month a date moved is, where it is one: the date whose
     *                     month it is, and the months it is on from it
     */
    static Read of(Core e, InputReads at, Symbols symbols, DeclarationNewtypes newtypes,
                   Function<DateMonthMoves.Step, MonthStart> monthStartOf) {
        if (!(Core.withoutStanding(e) instanceof Core.PreservedCall call)) {
            return null;
        }
        DateMonthMoves.Step moved = DateMonthMoves.stepOf(call,
                each -> at.folded(each, symbols, newtypes));
        MonthMoveCases.Asked asked = MonthMoveCases.Asked.DAY_NUMBER;
        if (moved == null) {
            moved = ofWhichItIsAPart(call, at, symbols, newtypes);
            if (moved == null) {
                return null;
            }
            asked = askedOf(call, moved);
        }
        // Where the date moved is the first of a month, it is in the month and year of the date it
        // is the first of the month of, has no day of its own to state, and is moved by the months
        // it is on from that month as well.
        MonthStart start = monthStartOf.apply(moved);
        long months = start == null ? moved.months() : moved.months() + start.moved();
        List<MonthMoveCases.Case> cases = MonthMoveCases.of(months, asked, start != null);
        if (cases == null || !(moved.law().operation().operation()
                instanceof ValueName.Stdlib move)) {
            return null;
        }
        Atoms atoms = new Atoms(call, moved, start == null ? moved.date() : start.of());
        List<Choice.ADefinitionCase> out = new ArrayList<>(cases.size());
        for (MonthMoveCases.Case each : cases) {
            List<Choice.FormsStand> given = new ArrayList<>();
            for (MonthMoveCases.Stand stand : each.given()) {
                given.add(new Choice.FormsStand(LinearForm.atom(atoms.of(stand.of())),
                        stand.rel(), LinearForm.constant(ExactRatio.of(stand.value()))));
            }
            out.add(new Choice.ADefinitionCase(answerOf(each, atoms, start != null), given));
        }
        return new Read(call, move, out);
    }

    /**
     * What {@code each} answers, as a form of the numbers of the date. Where the date is the first
     * of a month, the day count its case moves is the first of the month of the date it is the
     * first of: that date's day count less its day of the month, and one.
     */
    private static LinearForm<Core> answerOf(MonthMoveCases.Case each, Atoms atoms,
                                             boolean ofAMonthStart) {
        Map<Core, ExactRatio> weights = new LinkedHashMap<>();
        long constant = each.constant();
        for (Map.Entry<MonthMoveCases.Of, Long> weight : each.weights().entrySet()) {
            ExactRatio by = ExactRatio.of(weight.getValue());
            if (ofAMonthStart && weight.getKey() == MonthMoveCases.Of.DAY_NUMBER) {
                weights.put(atoms.of(MonthMoveCases.Of.DAY_OF_MONTH), by.negated());
                constant += weight.getValue();
            }
            weights.put(atoms.of(weight.getKey()), by);
        }
        return new LinearForm<>(ExactRatio.of(constant), weights);
    }

    /** Which number of the moved date {@code call} takes, of the move {@code step}. */
    private static MonthMoveCases.Asked askedOf(Core.PreservedCall call,
                                                DateMonthMoves.Step step) {
        if (call.operation().equals(step.law().day().operation())) {
            return MonthMoveCases.Asked.DAY_OF_MONTH;
        }
        return call.operation().equals(step.law().year().operation())
                ? MonthMoveCases.Asked.YEAR : MonthMoveCases.Asked.MONTH;
    }

    /** The move {@code call}, the day, the month or the year of a date, takes a number of — or
     *  null where it is no such number of a move read where {@code call} is. */
    private static DateMonthMoves.Step ofWhichItIsAPart(Core.PreservedCall call, InputReads at,
                                                        Symbols symbols,
                                                        DeclarationNewtypes newtypes) {
        if (call.args().size() != 1) {
            return null;
        }
        Denotation date = at.standing(call.args().getFirst(), symbols, newtypes);
        DateMonthMoves.Step step = DateMonthMoves.stepOf(date.value(),
                each -> date.at().folded(each, symbols, newtypes));
        // What the cases are stated of is the date the move is made from. It is written where
        // the move is, which is outside what the call stands inside of, so it reads the same here.
        if (step == null) {
            return null;
        }
        boolean aNumberOfIt = call.operation().equals(step.law().day().operation())
                || call.operation().equals(step.law().year().operation())
                || call.operation().equals(step.law().month().operation());
        if (!aNumberOfIt) {
            return null;
        }
        return step;
    }

    /**
     * The numbers of the date a move is made from, as the calls that state them: one call for
     * each number however many cases state it, so that the cases are over the same nodes.
     */
    private static final class Atoms {

        private final Core.PreservedCall basis;
        private final DateMonthMoves.Step step;
        private final Core partsOf;
        private final Map<MonthMoveCases.Of, Core> made = new EnumMap<>(MonthMoveCases.Of.class);

        /** @param partsOf the date whose day count, month, year and day state the cases: the date
         *                 moved, or the date it is the first of the month of */
        Atoms(Core.PreservedCall basis, DateMonthMoves.Step step, Core partsOf) {
            this.basis = basis;
            this.step = step;
            this.partsOf = partsOf;
        }

        Core of(MonthMoveCases.Of of) {
            Core held = made.get(of);
            if (held == null) {
                held = make(of);
                made.put(of, held);
            }
            return held;
        }

        private Core make(MonthMoveCases.Of of) {
            return switch (of) {
                case DAY_NUMBER -> partsOf;
                case MONTH -> call(step.law().month(), List.of(partsOf), of);
                case YEAR -> call(step.law().year(), List.of(partsOf), of);
                case DAY_OF_MONTH -> call(step.law().day(), List.of(partsOf), of);
                case YEAR_BY_4 -> remainder(4, of);
                case YEAR_BY_100 -> remainder(100, of);
                case YEAR_BY_400 -> remainder(400, of);
            };
        }

        private Core remainder(long divisor, MonthMoveCases.Of of) {
            return call(step.law().remainder(), List.of(of(MonthMoveCases.Of.YEAR),
                    new Core.Int(divisor, Type.INT, basis.pos())), of);
        }

        /** A call no source wrote, derived from the move's, one for each number of the date. */
        private Core call(DeclaredOperation operation, List<Core> args, MonthMoveCases.Of of) {
            int ordinal = of.ordinal();
            ApplicationOrigin application = ApplicationOrigin.composedOutOf(basis.application(),
                    ordinal, ApplicationDerivationCause.NumberOfADateMoved::new);
            ReferenceOrigin reference = ReferenceOrigin.composedOutOf(basis.reference(), ordinal,
                    ReferenceDerivationCause.NumberOfADateMovedReference::new);
            return new Core.PreservedCall(operation, args,
                    new Core.KeptCallPlace(reference, application, basis.place().lineage()),
                    Core.KernelFact.None.INSTANCE, Type.INT, basis.pos());
        }
    }
}
