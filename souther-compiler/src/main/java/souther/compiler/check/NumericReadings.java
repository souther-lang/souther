package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.NumericResult;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.semantics.TakenAs;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * Which representations read the number an operation answers, and how many of them there are.
 *
 * <p>Three sentences say what this is for, and each of them is a decision somebody will want to
 * undo:
 *
 * <ul>
 *   <li>This describes facts, not precedence. There is no first arm and no fallback: an operation
 *       carrying two accounts of its number gets two, and choosing between them here would be a
 *       fifth account nobody declared.
 *   <li>{@link Resolution.Multiple} is an invalid library definition, not a choice to resolve. What
 *       it means is that two representations would each read one call and which of them a report
 *       showed would be whichever reader arrived. Nothing recovers from it.
 *   <li>{@link Resolution.None} is valid globally; a question may make it invalid within its range.
 *       Most of the library answers numbers nothing reads, and that is ordinary. Where a check
 *       needs a reading, it is that check's range that says so and its silence
 *       ({@code OperationFact.SaysNothingOf}) that is the other answer.
 * </ul>
 *
 * <p>The third is the one worth keeping. Made to answer {@code One} wherever a number is answered,
 * this would start carrying the deliberate silences — {@code String.toInt} answers a number at one
 * case of a union and no representation reads it there — and finding out what is declared would be
 * deciding what ought to be. Made to refuse {@code Multiple} only where some question asks, the
 * exclusivity would hold as far as that question's range and no further, and would move when the
 * range moved.
 *
 * <p><b>Counted, and not asked one representation at a time.</b> Written as a condition per
 * representation inside whatever holds a declaration ({@link DischargeRules#holdTakenOf}), a
 * representation added is one every existing representation has to be told about, and the pair
 * nobody writes down is the pair that goes unchecked. Counted here, an account added is one arm on
 * {@link NumericReading} and one line here, and every pair it makes with an existing arm is refused
 * without being named.
 */
final class NumericReadings {

    /** How many representations read one operation's number. */
    sealed interface Resolution {

        /** Nothing reads it. */
        record None() implements Resolution {}

        /** Exactly one does, and this is it. */
        record One(NumericReading reading) implements Resolution {

            public One {
                java.util.Objects.requireNonNull(reading, "there is one, so it is named");
            }
        }

        /** More than one does, which the library must not declare. */
        record Multiple(List<NumericReading> readings) implements Resolution {

            public Multiple {
                readings = List.copyOf(readings);
                if (readings.size() < 2) {
                    throw new IllegalArgumentException(
                            "more than one is more than one: " + readings.size() + " named");
                }
            }
        }
    }

    /**
     * The representations that read the number {@code operation} answers, counted, over the
     * declarations in {@code declared}.
     *
     * <p>Over a source that is handed in and not over the table the process happens to hold. What
     * holds the declarations to the library is given its source for the same reason
     * ({@code OperationFactBinder#bindAll}): a fact reaches it before it reaches any table, so a
     * check reading the table instead would be blind to exactly the declaration being held. It
     * would also be asking that table to finish building while it was being built.
     *
     * @throws IllegalStateException where the library declares no such operation
     */
    static Resolution resolve(Stdlib stdlib, List<OperationFacts.Declared> declared,
            ValueName operation) {
        List<NumericReading> found = readingsOf(stdlib, declared, operation);
        return switch (found.size()) {
            case 0 -> new Resolution.None();
            case 1 -> new Resolution.One(found.get(0));
            default -> new Resolution.Multiple(found);
        };
    }

    /**
     * The same, listed.
     *
     * <p>The subject is the number, so an operation that answers none has no reading of one — a
     * date shifted by an amount is declared as a form of what its arguments are counted as, and
     * that form is about the date and not about a number the operation answered. Read without this,
     * every such operation would carry a reading of a number that is not there, and a proposition
     * with no subject is one nothing can be false of.
     *
     * <p>Answered at one case of a union counts, for the reason {@code Question.NUMERIC_RESULT}
     * counts it: what the shape of a result says is which inputs an operation declines, not what
     * it answers where it answers anything.
     *
     * <p>In the order the arms are written and not in the order the facts were declared, so a
     * message naming two readings names them the same way whichever of them was written first.
     */
    private static List<NumericReading> readingsOf(Stdlib stdlib,
            List<OperationFacts.Declared> declared, ValueName operation) {
        Stdlib.Entry entry = DischargeRules.holdTheOperationToTheLibrary(stdlib, operation);
        if (NumericAnswers.in(entry.signature().result()) == null) {
            return List.of();
        }
        List<NumericReading> terms = new ArrayList<>();
        List<NumericReading> forms = new ArrayList<>();
        List<NumericReading> arithmetic = new ArrayList<>();
        for (OperationFacts.Declared each : declared) {
            if (!operation.equals(each.operation())) {
                continue;
            }
            // No default. A kind of fact added is a kind this has to answer for — whether it is an
            // account of the number an operation answers is a question about the fact, and one
            // nobody would think to come here and ask. Answered by falling through a default, the
            // fifth representation would be exclusive with nothing.
            switch (each.fact()) {
                case OperationFact.AnswersANumberTakenOfTheOneValueItIsGiven(TakenAs how) ->
                        terms.add(new NumericReading.AsATermTakenOfItsArgument(how));
                case OperationFact.AnswersAFormOfItsArguments(
                        NumericDomain.LinearForm<ArgumentRef> form) ->
                        forms.add(new NumericReading.AsAFormOfItsArguments(form));
                case OperationFact.ComputesANumber(NumericResult result) ->
                        arithmetic.add(new NumericReading.AsTheArithmeticItComputes(result));
                // The cases a definition is written in name which argument is answered under which
                // relation between the arguments. A reader still reads the argument, so what the
                // call answers has no account of its own here — and every operation carrying one
                // today is written in the language as well, so nothing here has to tell the two
                // apart.
                case OperationFact.IsDefinedByCases _,
                     // The rest say something else about the operation: where a number runs, what
                     // an operation keeps of a container, what a predicate travels through, what a
                     // shift is stated through, whether every answer has a value that gives it.
                     // None of them is a way of reading the number a call answered.
                     OperationFact.BoundsItsResult _,
                     OperationFact.StatesTheOrderOfItsArguments _,
                     OperationFact.ShiftsBy _,
                     OperationFact.BuildsItsResultFrom _,
                     OperationFact.ResultIsNoSmallerThan _,
                     OperationFact.ReadsItsContainer _,
                     OperationFact.IsStatedOverAProjection _,
                     OperationFact.StatesItsPredicateOfEveryElement _,
                     OperationFact.MeansTheSameAsASizeOfNought _,
                     OperationFact.EveryAnswerItCanGiveHasASourceValue _,
                     OperationFact.SaysNothingOf _ -> { }
            }
        }
        List<NumericReading> found = new ArrayList<>(terms);
        found.addAll(forms);
        found.addAll(arithmetic);
        if (!(entry.declaration().body() instanceof Hir.FnBody.Intrinsic)) {
            found.add(new NumericReading.ByTheBodyTheLanguageWritesOut());
        }
        return List.copyOf(found);
    }

    /** What reads it, for a message that names the readings there are. */
    static String describe(Resolution resolution) {
        return switch (resolution) {
            case Resolution.None _ -> "nothing";
            case Resolution.One(NumericReading one) -> one.describes();
            case Resolution.Multiple(List<NumericReading> readings) -> String.join(" and ",
                    readings.stream().map(NumericReading::describes).toList());
        };
    }

    private NumericReadings() {}
}
