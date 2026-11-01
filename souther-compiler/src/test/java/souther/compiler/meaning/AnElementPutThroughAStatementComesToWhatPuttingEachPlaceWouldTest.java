package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The element of a list of whole numbers put at a value through a statement
 * ({@link OnOneElement#at}, {@link OnOneElement#inItsRemainders}) comes to what putting it at
 * each place the statement holds, and joining every conjunction, disjunction, statement read where
 * an operation answers and quantifier again of what each holds put, comes to — or to nothing in
 * both where the value cannot be held at some place.
 *
 * <p>The second is written out here as a walk of the statement as a tree, each comparison put on
 * its own; the first meets a part shared by several places once and hands back a part it changed
 * nothing in. Drawn at random from a fixed seed: remainders of the element and a number of the
 * input moved by a constant, the element weighed itself, the number alone, truths, held together
 * and as alternatives, denied, read where a truth answers and said of some element of a
 * container — the same part met again in several places. Put at whole numbers, and at halves,
 * which leave a remainder's dividend no whole number to be divided.
 */
class AnElementPutThroughAStatementComesToWhatPuttingEachPlaceWouldTest {

    private static final NumericTerm X = new NumericTerm.ValueOf(TermPath.of("x"));
    private static final Quantity INPUT = new DecisionAtom.OfTheInput(X);
    private static final Quantity.OfABinding ELEMENT = new Quantity.OfABinding(
            new BindingId(new BindingOwner.OfValue("demo", "f"), 0), List.of(), Type.INT,
            Optional.empty(), Optional.of(new Quantity.AWholeNumberInTurn(
                    LinearForm.constant(ExactRatio.ZERO),
                    new LinearForm<>(ExactRatio.ZERO, Map.of(X, ExactRatio.ONE)))));
    private static final ValueName FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");
    private static final DecisionSubject CONTAINER = new DecisionSubject.AnInput(
            TermPath.of("ys"));
    private static final List<String> AT = List.of("a", "b");

    @Test
    void puttingTheElementComesToWhatPuttingEachPlaceWould() {
        Random random = new Random(2937);
        int cannot = 0;
        int changed = 0;
        for (int drawn = 0; drawn < 3000; drawn++) {
            Proposition stated = statement(random, 4, new ArrayList<>(), true);
            ExactRatio value = random.nextInt(5) == 0
                    ? ExactRatio.of(BigInteger.valueOf(random.nextInt(9) - 4), BigInteger.TWO)
                    : ExactRatio.of(random.nextInt(25) - 5);
            LinearForm<Quantity> there = LinearForm.constant(value);
            for (boolean itself : new boolean[] {true, false}) {
                Proposition expected = putAgain(stated, there, itself);
                Proposition put = itself ? OnOneElement.at(stated, ELEMENT, there)
                        : OnOneElement.inItsRemainders(stated, ELEMENT, there);
                String said = (itself ? "at " : "in its remainders at ") + value + " through "
                        + stated.spelling();
                assertEquals(expected == null ? null : expected.spelling(),
                        put == null ? null : put.spelling(), said);
                assertEquals(expected, put, said);
                cannot += put == null ? 1 : 0;
                changed += put != null && put != stated ? 1 : 0;
            }
        }
        assertTrue(cannot > 0, "some value is one a place cannot hold");
        assertTrue(changed > 0, "some putting changes the statement");
    }

    /** What putting the element at {@code there} through {@code stated} comes to when each
     *  place is put on its own and every part joined again: a walk of it as a tree. */
    private static Proposition putAgain(Proposition stated, LinearForm<Quantity> there,
                                        boolean itself) {
        return switch (stated) {
            case Proposition.All all -> {
                List<Proposition> each = putAgain(all.parts(), there, itself);
                yield each == null ? null : Proposition.all(each);
            }
            case Proposition.Any any -> {
                List<Proposition> each = putAgain(any.parts(), there, itself);
                yield each == null ? null : Proposition.any(each);
            }
            case Proposition.WhereItAnswers where -> {
                Proposition answers = putAgain(where.answers(), there, itself);
                Proposition states = putAgain(where.states(), there, itself);
                yield answers == null || states == null ? null
                        : Proposition.whereItAnswers(answers, states);
            }
            case Proposition.Some some -> {
                Proposition met = putAgain(some.ofTheElement(), there, itself);
                yield met == null ? null : new Proposition.Some(some.container(), met, some.holds());
            }
            default -> itself ? OnOneElement.at(stated, ELEMENT, there)
                    : OnOneElement.inItsRemainders(stated, ELEMENT, there);
        };
    }

    private static List<Proposition> putAgain(List<Proposition> parts,
                                              LinearForm<Quantity> there, boolean itself) {
        List<Proposition> out = new ArrayList<>();
        for (Proposition part : parts) {
            Proposition one = putAgain(part, there, itself);
            if (one == null) {
                return null;
            }
            out.add(one);
        }
        return out;
    }

    /** A statement drawn at random, a part met before drawn again now and then; a quantifier
     *  or a statement read where a truth answers only where {@code mayQuantify}, which inside a
     *  quantifier it is not. */
    private static Proposition statement(Random random, int depth, List<Proposition> met,
                                         boolean mayQuantify) {
        if (!met.isEmpty() && random.nextInt(4) == 0) {
            return met.get(random.nextInt(met.size()));
        }
        int kind = random.nextInt(depth == 0 ? 2 : 7);
        Proposition out = switch (kind) {
            case 0 -> comparison(random);
            case 1 -> new Proposition.Truth(new DecisionSubject.AnInput(
                    TermPath.of(AT.get(random.nextInt(AT.size())))), random.nextBoolean());
            case 2, 3 -> {
                List<Proposition> parts = new ArrayList<>();
                for (int at = 0; at < 2 + random.nextInt(3); at++) {
                    parts.add(statement(random, depth - 1, met, mayQuantify));
                }
                yield kind == 2 ? Proposition.all(parts) : Proposition.any(parts);
            }
            case 4 -> statement(random, depth - 1, met, mayQuantify).denied();
            case 5 -> mayQuantify ? Proposition.whereItAnswers(new Proposition.Truth(
                    new DecisionSubject.AnInput(TermPath.of("c")), true),
                    statement(random, depth - 1, met, true)) : comparison(random);
            default -> mayQuantify
                    ? new Proposition.Some(CONTAINER, statement(random, depth - 1,
                            new ArrayList<>(), false), random.nextBoolean())
                    : comparison(random);
        };
        met.add(out);
        return out;
    }

    /** A comparison of a remainder of the element and the input's number, of the element
     *  weighed itself beside the number, or of the number alone. */
    private static Proposition comparison(Random random) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        switch (random.nextInt(3)) {
            case 0 -> {
                Map<Quantity, ExactRatio> dividend = new LinkedHashMap<>();
                dividend.put(ELEMENT, ExactRatio.of(random.nextInt(5) - 2));
                if (random.nextBoolean()) {
                    dividend.put(INPUT, ExactRatio.ONE);
                }
                dividend.values().removeIf(each -> each.signum() == 0);
                if (dividend.isEmpty()) {
                    dividend.put(ELEMENT, ExactRatio.ONE);
                }
                coefs.put(new Quantity.RemainderOfADividend(FLOOR_MOD,
                        new LinearForm<>(ExactRatio.of(random.nextInt(9) - 4), dividend),
                        BigInteger.valueOf(2 + random.nextInt(6))), ExactRatio.ONE);
            }
            case 1 -> {
                coefs.put(ELEMENT, ExactRatio.ONE);
                coefs.put(INPUT, ExactRatio.of(-1));
            }
            default -> coefs.put(INPUT, ExactRatio.ONE);
        }
        Relation.OneWay<Quantity> one = Relation.OneWay.of(
                new LinearForm<>(ExactRatio.of(random.nextInt(9) - 4), coefs),
                new Rel[] {Rel.GE, Rel.GT, Rel.EQ}[random.nextInt(3)]);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds() == random.nextBoolean());
    }
}
