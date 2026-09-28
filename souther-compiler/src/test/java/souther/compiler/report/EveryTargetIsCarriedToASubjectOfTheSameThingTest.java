package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.RowRef;
import souther.compiler.observe.Target;
import souther.compiler.source.SourceId;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a reason is about is carried to the document as the same thing.
 *
 * <p>One {@code switch} turns what a reason holds into what a document writes, and javac holds it to
 * having an arm per kind and to nothing else: two arms swapped is a program that compiles and a
 * document that says a reason is about something it is not. The arms are not alike enough for that
 * to show up downstream either — a source and a row are written under different keys, so the
 * document would be refused by its own schema, while a behavior and a module are written the same
 * way and would ship.
 *
 * <p>Every kind, and the check says so by asking the sum what its kinds are. A kind added arrives
 * here as a kind nothing above carries rather than as a case nobody thought about.
 */
class EveryTargetIsCarriedToASubjectOfTheSameThingTest {

    private static final SourceId SOURCE = new SourceId("3");

    private static final RowRef ROW =
            new RowRef("take", SOURCE, new RowIdentity.Unnamed(2));

    /** One of each kind, and what a document is to say it is about. */
    private static Map<Target, Subject> carried() {
        Map<Target, Subject> out = new LinkedHashMap<>();
        out.put(new Target.OfBehavior("take"), new Subject.OfABehavior("take"));
        out.put(new Target.OfModule("example.split"), new Subject.OfAModule("example.split"));
        out.put(new Target.OfSource(SOURCE), new Subject.OfASource(SOURCE));
        out.put(new Target.OfRow(ROW), new Subject.OfARow(ROW));
        out.put(new Target.AtPosition("take", "request.cost"),
                new Subject.AtASpelledPosition("take", "request.cost"));
        return out;
    }

    @Test
    void everyKindOfTargetIsCarriedToTheSubjectOfWhatItIsAbout() {
        carried().forEach((target, subject) ->
                assertEquals(subject, Subjects.of(target), () -> "what " + target + " is about"));
    }

    /** And the kinds above are the kinds there are. */
    @Test
    void oneOfEveryKindIsCarried() {
        Set<Class<?>> built = new LinkedHashSet<>();
        carried().keySet().forEach(target -> built.add(target.getClass()));

        assertEquals(Set.of(Target.class.getPermittedSubclasses()), built,
                "a kind of thing a reason can be about that nothing here carries");
    }
}
