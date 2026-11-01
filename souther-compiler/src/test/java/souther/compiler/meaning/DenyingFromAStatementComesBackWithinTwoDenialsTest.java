package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Denying from a statement on comes back, within two denials, to a statement met before.
 *
 * <p>Not always to the statement itself: joining is no normal form, and two statements saying the
 * same, spelled two ways, can have one denial. A reader naming one column by a statement and its
 * denial walks the denials until one comes back ({@code DecisionCondition.AStatement#of}), and
 * the walk ends because each denial is kept both ways. Some statement drawn here does come back
 * spelled another way, so the walk is held where it is needed.
 *
 * <p>Drawn at random from a fixed seed: truths and comparisons, said to hold and not to, held
 * together and as alternatives, denied, read where a truth answers, counted, and said of some
 * element of a container — among them statements joining writes by the cases of a condition,
 * whose denial is written another way.
 */
class DenyingFromAStatementComesBackWithinTwoDenialsTest {

    private static final List<String> AT = List.of("a", "b", "c");
    private static final DecisionSubject CONTAINER = new DecisionSubject.AnInput(
            TermPath.of("xs"));

    @Test
    void denyingFromAStatementComesBackWithinTwoDenials() {
        Random random = new Random(2937);
        int other = 0;
        for (int drawn = 0; drawn < 3000; drawn++) {
            Proposition stated = statement(random, 4, true);
            Proposition once = stated.denied();
            Proposition twice = once.denied();
            Proposition thrice = twice.denied();
            assertEquals(once.spelling(), thrice.spelling(), () -> stated.spelling() + " denied "
                    + once.spelling() + ", then " + twice.spelling());
            other += twice.spelling().equals(stated.spelling()) ? 0 : 1;
        }
        // Some statement is spelled another way denied twice, which is the walk this holds.
        assertTrue(other > 0, "every statement came back as itself");
    }

    private static Proposition statement(Random random, int depth, boolean mayQuantify) {
        int kind = random.nextInt(depth == 0 ? 2 : 8);
        return switch (kind) {
            case 0 -> truth(random);
            case 1 -> comparison(random);
            case 2, 3 -> {
                List<Proposition> parts = new ArrayList<>();
                for (int at = 0; at < 2 + random.nextInt(3); at++) {
                    parts.add(statement(random, depth - 1, mayQuantify));
                }
                yield kind == 2 ? Proposition.all(parts) : Proposition.any(parts);
            }
            case 4 -> statement(random, depth - 1, mayQuantify).denied();
            // A condition and what each way of it comes to, as joining an if writes it.
            case 5 -> {
                Proposition condition = truth(random);
                yield Proposition.any(List.of(
                        Proposition.all(List.of(condition,
                                statement(random, depth - 1, mayQuantify))),
                        Proposition.all(List.of(condition.denied(),
                                statement(random, depth - 1, mayQuantify)))));
            }
            case 6 -> mayQuantify ? Proposition.whereItAnswers(truth(random),
                    statement(random, depth - 1, true)) : counted(random);
            default -> mayQuantify
                    ? new Proposition.Some(CONTAINER,
                            statement(random, depth - 1, false), random.nextBoolean())
                    : counted(random);
        };
    }

    private static Proposition truth(Random random) {
        return new Proposition.Truth(new DecisionSubject.AnInput(
                TermPath.of(AT.get(random.nextInt(AT.size())))), random.nextBoolean());
    }

    private static Proposition comparison(Random random) {
        DecisionAtom at = new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("n")));
        Relation.OneWay<Quantity> one = Relation.OneWay.of(
                new LinearForm<>(ExactRatio.of(random.nextInt(5) - 2), Map.of(at, ExactRatio.ONE)),
                new Rel[] {Rel.GE, Rel.GT, Rel.EQ}[random.nextInt(3)]);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds() == random.nextBoolean());
    }

    /** How many of two or three truths of different positions hold, one of them or more. */
    private static Proposition counted(Random random) {
        TreeMap<Spelling, Proposition> bySpelling = new TreeMap<>();
        for (int at = 0; at < 3; at++) {
            Proposition one = truth(random);
            bySpelling.put(one.spelling(), one);
        }
        if (bySpelling.size() < 2) {
            return truth(random);
        }
        List<Proposition> statements = List.copyOf(bySpelling.values());
        return new Proposition.SoManyHold(statements, statements.stream().map(_ -> 1).toList(),
                List.of(1));
    }
}
