package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Text;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The values a statement names at the places it reads, which are the values it tells apart there.
 *
 * <p>A statement over a place is true of some values of it and false of others, and the values
 * that say so are the ones it was written with: {@code qty > 5} is told apart at five and at the
 * whole numbers beside it, {@code code == "USD"} at {@code "USD"}. What a type tells apart is
 * another answer ({@code Witnesses#distinctValuesOf}), and a type states nothing of five: a
 * search for an element the statement holds of and one it fails of that is handed only the type's
 * values meets a statement written with a constant by chance.
 *
 * <p>A value is the number or the text, and nothing of how it is written: which fixture it
 * becomes is the type of the place it is named at, an {@code Int} or a {@code Decimal}, which the
 * language does not convert between ({@link Partitions#writtenNumberAt}).
 *
 * <p>Named at a place only where the statement compares the value at that place: the number of a
 * place itself, which is what a comparison written with a constant tells apart. A measure of a
 * place — how many characters it holds, how many elements — is no value of it, and a value its
 * comparison names is no value to put there; nothing is named for one, since what would be is
 * the place built to have that measure, which a measure alone does not say.
 *
 * <p>Each form of statement is said here, by the exhaustive switch below, to name values or to
 * name none, so that a form added to {@link Proposition} stops the build here until somebody says
 * which. A form that names none is told apart some other way — a case, a truth, a presence by what
 * the type divides into — or is not read by this at all; the statement is then met where the
 * values of the type or a row of the model happen to meet it, and nothing is shown otherwise.
 *
 * <p>Only a statement over one place alone names values for it: a comparison of two places
 * ({@code x + y > 5}) is told apart by values that stand in a relation to one another, which no
 * place names by itself.
 */
final class ValuesAStatementNames {

    private ValuesAStatementNames() {}

    /** A value a statement names: the number or the text it is written with. */
    sealed interface Named {

        /** A number, exactly: the same at an {@code Int} place and at a {@code Decimal} one. */
        record Numeric(BigDecimal at) implements Named {}

        /** A text. */
        record Written(String at) implements Named {}
    }

    /**
     * Each place {@code stated} names values at, and the values in the order they are named: the
     * value a comparison is written with, and the whole numbers beside it a comparison to a number
     * is told apart at.
     */
    static Map<TermPath, List<Named>> of(Proposition stated) {
        Map<TermPath, List<Named>> out = new LinkedHashMap<>();
        collect(stated, out);
        return out;
    }

    private static void collect(Proposition stated, Map<TermPath, List<Named>> out) {
        switch (stated) {
            case Proposition.Compared compared -> relation(compared.relation(), out);
            case Proposition.All all -> all.parts().forEach(each -> collect(each, out));
            case Proposition.Any any -> any.parts().forEach(each -> collect(each, out));
            case Proposition.Some some -> collect(some.ofTheElement(), out);
            case Proposition.WhereItAnswers answers -> {
                collect(answers.answers(), out);
                collect(answers.states(), out);
            }
            case Proposition.SoManyHold counted ->
                    counted.statements().forEach(each -> collect(each, out));
            case Proposition.OnAnApplication applied ->
                    applied.each().forEach(each -> collect(each, out));
            case Proposition.Always _, Proposition.Truth _, Proposition.InCases _,
                 Proposition.Present _, Proposition.InTheStrings _, Proposition.SameValue _,
                 Proposition.StringInside _, Proposition.LastToHold _, Proposition.OfTheWays _,
                 Proposition.Carried _, Proposition.SomeReachable _, Proposition.Unread _ -> { }
        }
    }

    private static void relation(Relation relation, Map<TermPath, List<Named>> out) {
        switch (relation) {
            // A place written with a value on the order it stands on: the value, and where it
            // counts the whole numbers beside it, which a strict order is told apart at.
            case Relation.Ordered(DecisionAtom term, Place at, var _) -> {
                TermPath place = valueAt(term);
                if (place != null) {
                    switch (at) {
                        case Count count -> named(place, besideThe(count.at()), out);
                        case Text text -> named(place, List.of(new Named.Written(text.at())), out);
                    }
                }
            }
            // One place weighed against a constant: it is told apart where the form is nought,
            // and at the whole numbers either side of it.
            case Relation.Affine(var form, var _) -> {
                if (form.coefs().size() != 1) {
                    return;
                }
                Map.Entry<Quantity, ExactRatio> only = form.coefs().entrySet().iterator().next();
                TermPath place = only.getKey() instanceof DecisionAtom atom ? valueAt(atom) : null;
                if (place != null && form.constant().negated().dividedBy(only.getValue())
                        instanceof ExactAnswer.Held<ExactRatio>(ExactRatio where)) {
                    named(place, wholesBeside(where), out);
                }
            }
        }
    }

    /** The place {@code term} is the value at, or null where it is a measure of a place, a number
     *  of several, or of none. */
    private static TermPath valueAt(DecisionAtom term) {
        return term instanceof DecisionAtom.OfTheInput(NumericTerm.ValueOf value, var _)
                ? value.position() : null;
    }

    /** {@code at}, and the whole numbers either side of it — the number itself too where it is no
     *  whole number. */
    private static List<Named> besideThe(BigDecimal at) {
        ExactRatio exact = ExactRatio.of(at);
        List<Named> out = new ArrayList<>();
        if (!exact.isWhole()) {
            out.add(new Named.Numeric(at));
        }
        wholesBeside(exact).forEach(written -> {
            if (!out.contains(written)) {
                out.add(written);
            }
        });
        return out;
    }

    /** The whole numbers at and either side of {@code at}: the one above, the one below, and the
     *  next past each. */
    private static List<Named> wholesBeside(ExactRatio at) {
        if (!(at.floor() instanceof ExactAnswer.Held<BigInteger>(BigInteger below))
                || !(at.ceiling() instanceof ExactAnswer.Held<BigInteger>(BigInteger above))) {
            return List.of();
        }
        List<Named> out = new ArrayList<>();
        for (BigInteger each : List.of(above, below, above.add(BigInteger.ONE),
                below.subtract(BigInteger.ONE))) {
            Named written = new Named.Numeric(new BigDecimal(each));
            if (!out.contains(written)) {
                out.add(written);
            }
        }
        return out;
    }

    private static void named(TermPath place, List<Named> values, Map<TermPath, List<Named>> out) {
        List<Named> at = out.computeIfAbsent(place, _ -> new ArrayList<>());
        values.stream().filter(value -> !at.contains(value)).forEach(at::add);
    }
}
