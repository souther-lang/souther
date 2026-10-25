package souther.compiler.meaning;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * What a statement holds the values of the input to wherever it holds: which cases a value is, or
 * is not, and which truth a value is.
 *
 * <p>What every row the statement holds of is, and nothing that only some of them are. Read through
 * the whole of the statement and not off its outermost parts: where it is one of several things,
 * what it holds a value to is what each of them holds it to, taken together — the first term
 * where some {@code q} holds, or the first term where it does not, is the first term. A statement
 * one of whose ways says nothing of a value says nothing of it.
 *
 * <p>A value it holds to nothing is left out, so what is said is never more than what a row has to
 * be: where a statement is a relation, or one way of it does not ask which case a value is, the
 * row may be anything there.
 */
public final class CasesHeldTo {

    /** What one value of the input is held to. */
    public sealed interface Held {

        /** One of {@code cases}: one of some cases of a sum, holding a value or none. */
        record OneOf(CasesLeft cases) implements Held {

            public OneOf {
                Objects.requireNonNull(cases, "a value held to some cases is held to one at least");
            }
        }

        /** None of {@code cases}. */
        record NoneOf(CasesLeft cases) implements Held {

            public NoneOf {
                Objects.requireNonNull(cases, "a value held out of some cases is held out of one");
            }
        }

        /** The truth {@code holds}. */
        record ATruth(boolean holds) implements Held {}
    }

    private CasesHeldTo() {
    }

    /**
     * What {@code stated} holds each value of the input to, by the position of the value, in the
     * order the statement names them.
     */
    public static Map<TermPath, Held> of(Proposition stated) {
        Map<TermPath, Held> out = heldTo(stated);
        return out == null ? Map.of() : out;
    }

    /** The same, or null where {@code stated} holds nowhere. */
    private static Map<TermPath, Held> heldTo(Proposition stated) {
        return switch (stated) {
            case Proposition.Always(boolean holds) -> holds ? new LinkedHashMap<>() : null;
            case Proposition.WhereItAnswers where ->
                    heldTo(Proposition.all(List.of(where.answers(), where.states())));
            case Proposition.All all -> {
                Map<TermPath, Held> out = new LinkedHashMap<>();
                for (Proposition part : all.parts()) {
                    Map<TermPath, Held> each = heldTo(part);
                    if (each == null) {
                        yield null;
                    }
                    for (Map.Entry<TermPath, Held> one : each.entrySet()) {
                        Held before = out.get(one.getKey());
                        Held both = before == null ? one.getValue() : both(before, one.getValue());
                        if (both == null) {
                            yield null;
                        }
                        out.put(one.getKey(), both);
                    }
                }
                yield out;
            }
            case Proposition.Any any -> {
                Map<TermPath, Held> out = null;
                for (Proposition part : any.parts()) {
                    Map<TermPath, Held> each = heldTo(part);
                    if (each == null) {
                        continue;
                    }
                    out = out == null ? each : either(out, each);
                }
                yield out;
            }
            case Proposition.InCases(DecisionSubject.AnInput(TermPath of), CasesLeft cases,
                    boolean holds, var _) -> one(of, holds ? new Held.OneOf(cases)
                    : new Held.NoneOf(cases));
            case Proposition.Present(DecisionSubject.AnInput(TermPath of), boolean holds, var _) ->
                    one(of, new Held.OneOf(CasesLeft.of(Refinement.of(new Case.Presence(holds)))));
            case Proposition.Truth(DecisionSubject.AnInput(TermPath of), boolean holds, var _) ->
                    one(of, new Held.ATruth(holds));
            // A count of statements holds no value to anything here: less than it may, never more.
            case Proposition.InCases _, Proposition.Present _, Proposition.Truth _,
                 Proposition.Compared _, Proposition.InTheStrings _, Proposition.SameValue _,
                 Proposition.LastToHold _, Proposition.Some _, Proposition.Carried _,
                 Proposition.SomeReachable _, Proposition.Unread _, Proposition.OnAnApplication _,
                 Proposition.SoManyHold _ ->
                    new LinkedHashMap<>();
        };
    }

    private static Map<TermPath, Held> one(TermPath at, Held held) {
        Map<TermPath, Held> out = new LinkedHashMap<>();
        out.put(at, held);
        return out;
    }

    /** What a value held to {@code one} and to {@code other} is held to, or null where it can be
     *  neither. */
    private static Held both(Held one, Held other) {
        return switch (one) {
            case Held.OneOf(var in) -> switch (other) {
                case Held.OneOf(var also) -> oneOf(in.meet(also));
                case Held.NoneOf(var out) -> oneOf(less(in, out));
                case Held.ATruth _ -> one;
            };
            case Held.NoneOf(var out) -> switch (other) {
                case Held.OneOf(var in) -> oneOf(less(in, out));
                case Held.NoneOf(var also) -> new Held.NoneOf(union(out, also));
                case Held.ATruth _ -> one;
            };
            case Held.ATruth(var holds) -> other instanceof Held.ATruth(var also)
                    ? (holds == also ? one : null) : other;
        };
    }

    /** What a value held to {@code one} on some rows and to {@code other} on the rest is held to
     *  on all of them, or null where it is held to nothing. */
    private static Held eitherOf(Held one, Held other) {
        return switch (one) {
            case Held.OneOf(var in) -> switch (other) {
                case Held.OneOf(var also) -> new Held.OneOf(union(in, also));
                case Held.NoneOf(var out) -> noneOf(less(out, in));
                case Held.ATruth _ -> null;
            };
            case Held.NoneOf(var out) -> switch (other) {
                case Held.OneOf(var in) -> noneOf(less(out, in));
                case Held.NoneOf(var also) -> noneOf(out.meet(also));
                case Held.ATruth _ -> null;
            };
            case Held.ATruth(var holds) -> other instanceof Held.ATruth(var also) && holds == also
                    ? one : null;
        };
    }

    /** What {@code one} and {@code other} both hold a value to, each the statement on some rows. */
    private static Map<TermPath, Held> either(Map<TermPath, Held> one, Map<TermPath, Held> other) {
        Map<TermPath, Held> out = new LinkedHashMap<>();
        one.forEach((at, held) -> {
            Held also = other.get(at);
            Held both = also == null ? null : eitherOf(held, also);
            if (both != null) {
                out.put(at, both);
            }
        });
        return out;
    }

    private static Held oneOf(CasesLeft cases) {
        return cases == null ? null : new Held.OneOf(cases);
    }

    private static Held noneOf(CasesLeft cases) {
        return cases == null ? null : new Held.NoneOf(cases);
    }

    private static CasesLeft union(CasesLeft one, CasesLeft other) {
        List<Refinement> both = new ArrayList<>(one.atoms());
        other.atoms().stream().filter(atom -> !both.contains(atom)).forEach(both::add);
        return CasesLeft.ofEach(both);
    }

    private static CasesLeft less(CasesLeft from, CasesLeft out) {
        return CasesLeft.ofEach(from.atoms().stream()
                .filter(atom -> !out.atoms().contains(atom)).toList());
    }
}
