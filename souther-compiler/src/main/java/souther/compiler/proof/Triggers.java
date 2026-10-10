package souther.compiler.proof;

import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Where a statement holding of every value hands that value to an operation, or counts its
 * elements: which operation and at which of its arguments, or whether it is a container counted.
 *
 * <p>What a statement of every value is worth taking of is a value some other statement already
 * hands that operation there — a key a map is asked whether it holds is worth asking the statement
 * of keys of — or a container some other statement already counts the elements of, the same way;
 * and nothing else, since taking it of every value about would take it of values it says nothing
 * useful of, and there are many.
 */
final class Triggers {

    private Triggers() {}

    /** Each operation {@code statement} names an answer of with {@link Slot.Every} {@code which}
     *  among what it is handed, with the place it is handed there. */
    static Map<ValueName.Stdlib.Operation, Integer> of(LawProposition<Slot> statement, int which) {
        Map<ValueName.Stdlib.Operation, Integer> out = new LinkedHashMap<>();
        in(statement, which, out);
        return out;
    }

    /** Whether {@code statement} counts the elements of {@link Slot.Every} {@code which}. */
    static boolean counts(LawProposition<Slot> statement, int which) {
        boolean[] found = {false};
        Collect.counted(statement, container -> {
            if (container instanceof Slot.Every(int every) && every == which) {
                found[0] = true;
            }
        });
        return found[0];
    }

    private static void in(LawProposition<Slot> statement, int which,
                           Map<ValueName.Stdlib.Operation, Integer> out) {
        switch (statement) {
            case LawProposition.Always<Slot> _ -> { }
            case LawProposition.All<Slot>(var parts) -> parts.forEach(part -> in(part, which, out));
            case LawProposition.Any<Slot>(var parts) -> parts.forEach(part -> in(part, which, out));
            case LawProposition.Observed<Slot>(LawSubject<Slot> of, var _) -> in(of, which, out);
            case LawProposition.Compared<Slot>(LinearForm<LawNumber<Slot>> form, var _) ->
                    form.coefs().keySet().forEach(number -> in(number, which, out));
            case LawProposition.SomeElement<Slot>(var _, var ofTheElement, var _) ->
                    in(ofTheElement, which, out);
            case LawProposition.Same<Slot>(LawSubject<Slot> one, LawSubject<Slot> other, var _) -> {
                in(one, which, out);
                in(other, which, out);
            }
        }
    }

    private static void in(LawNumber<Slot> number, int which,
                           Map<ValueName.Stdlib.Operation, Integer> out) {
        switch (number) {
            case LawNumber.SizeOf<Slot>(LawSubject<Slot> of) -> in(of, which, out);
            case LawNumber.HowManyMeet<Slot>(var _, var ofTheElement) ->
                    in(ofTheElement, which, out);
            case LawNumber.HowManyDifferent<Slot>(var _, var ofTheElement) ->
                    in(ofTheElement, which, out);
            case LawNumber.SumOver<Slot>(var _, var ofTheElement) -> in(ofTheElement, which, out);
            case LawNumber.AnArgument<Slot> _ -> { }
        }
    }

    private static void in(LawSubject<Slot> subject, int which,
                           Map<ValueName.Stdlib.Operation, Integer> out) {
        if (subject instanceof LawSubject.AnswerOf<Slot>(var operation, List<LawSubject<Slot>> args)) {
            for (int at = 0; at < args.size(); at++) {
                if (args.get(at) instanceof LawSubject.Argument<Slot>(Slot.Every(int every))
                        && every == which) {
                    out.putIfAbsent(operation, at);
                }
                in(args.get(at), which, out);
            }
        }
    }
}
