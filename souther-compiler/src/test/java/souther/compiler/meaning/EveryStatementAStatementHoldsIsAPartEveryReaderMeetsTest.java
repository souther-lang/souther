package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.lang.reflect.ParameterizedType;
import java.lang.reflect.RecordComponent;
import java.lang.reflect.Type;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * Every statement a kind of statement holds in its components is one of the parts it says it
 * holds ({@link Proposition#partsHeld}), and its spelling tells two apart that differ in one.
 *
 * <p>Read off the components and not off a list kept here: a kind that comes to hold another
 * statement is a kind every reader of the parts has to meet, and the readers ask
 * {@code partsHeld} for them. A statement a search keeps of a node having nothing below was held
 * and met by none of them — not by the reader of what was left unread, nor by the count of what a
 * step concludes — until each was asked to read it.
 */
class EveryStatementAStatementHoldsIsAPartEveryReaderMeetsTest {

    private static Proposition truth(String at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(at)), true);
    }

    /** One of every kind that holds statements, each holding every one it can. */
    private static Map<Class<?>, Proposition> samples() {
        Map<Class<?>, Proposition> out = new LinkedHashMap<>();
        out.put(Proposition.WhereItAnswers.class,
                new Proposition.WhereItAnswers(truth("a"), truth("b")));
        out.put(Proposition.All.class, new Proposition.All(List.of(truth("a"), truth("b"))));
        out.put(Proposition.Any.class, new Proposition.Any(List.of(truth("a"), truth("b"))));
        out.put(Proposition.OnAnApplication.class,
                new Proposition.OnAnApplication(List.of(truth("a"), truth("b"))));
        out.put(Proposition.SoManyHold.class, new Proposition.SoManyHold(
                List.of(truth("a"), truth("b")), List.of(1, 2), List.of(1)));
        out.put(Proposition.Some.class, new Proposition.Some(
                new DecisionSubject.AnInput(TermPath.of("xs")), truth("a"), true));
        out.put(Proposition.SomeReachable.class, new Proposition.SomeReachable(TermPath.of("t"),
                TermPath.of("t"), List.of("children"), truth("t.a"),
                Optional.of(truth("t.leaf")), true));
        return out;
    }

    @Test
    void everyKindHoldingAStatementHasASampleHere() {
        Set<Class<?>> holding = new LinkedHashSet<>();
        for (Class<?> kind : Proposition.class.getPermittedSubclasses()) {
            for (RecordComponent component : kind.getRecordComponents()) {
                if (holdsStatements(component.getGenericType())) {
                    holding.add(kind);
                }
            }
        }
        assertEquals(holding, samples().keySet(), "a kind that holds statements and no sample here");
    }

    @Test
    void everyStatementInAComponentIsAPartHeld() throws Exception {
        for (Map.Entry<Class<?>, Proposition> each : samples().entrySet()) {
            List<Proposition> inComponents = new ArrayList<>();
            for (RecordComponent component : each.getKey().getRecordComponents()) {
                if (holdsStatements(component.getGenericType())) {
                    statementsIn(component.getAccessor().invoke(each.getValue()), inComponents);
                }
            }
            assertFalse(inComponents.isEmpty(), each.getKey().getSimpleName());
            assertEquals(inComponents, each.getValue().partsHeld(),
                    each.getKey().getSimpleName());
        }
    }

    /** Two searches told apart only by what is said of the node having nothing below are two. */
    @Test
    void aSearchIsSpelledWithWhatItSaysOfNothingBelow() {
        Proposition.SomeReachable one = new Proposition.SomeReachable(TermPath.of("t"),
                TermPath.of("t"), List.of("children"), truth("t.a"),
                Optional.of(truth("t.leaf")), true);
        Proposition.SomeReachable other = new Proposition.SomeReachable(TermPath.of("t"),
                TermPath.of("t"), List.of("children"), truth("t.a"),
                Optional.of(truth("t.empty")), true);
        Proposition.SomeReachable unsaid = new Proposition.SomeReachable(TermPath.of("t"),
                TermPath.of("t"), List.of("children"), truth("t.a"), Optional.empty(), true);

        assertNotEquals(one.key(), other.key());
        assertNotEquals(one.key(), unsaid.key());
    }

    /** A part nothing read where the node has nothing below is a part nothing read. */
    @Test
    void aStopWhereNothingIsBelowIsAStop() {
        WhyUnread why = new WhyUnread.NoNumberOnARun();
        Proposition.SomeReachable reached = new Proposition.SomeReachable(TermPath.of("t"),
                TermPath.of("t"), List.of("children"), truth("t.a"),
                Optional.of(new Proposition.Unread(Optional.empty(), 0, why, false, true)), true);

        assertEquals(List.of(why), Proposition.stopsIn(reached));
    }

    private static boolean holdsStatements(Type type) {
        if (type == Proposition.class) {
            return true;
        }
        return type instanceof ParameterizedType generic
                && (generic.getRawType() == List.class || generic.getRawType() == Optional.class)
                && generic.getActualTypeArguments()[0] == Proposition.class;
    }

    private static void statementsIn(Object component, List<Proposition> into) {
        switch (component) {
            case Proposition one -> into.add(one);
            case Optional<?> maybe -> maybe.ifPresent(one -> into.add((Proposition) one));
            case List<?> each -> each.forEach(one -> into.add((Proposition) one));
            default -> throw new IllegalArgumentException("no statement in " + component);
        }
    }
}
