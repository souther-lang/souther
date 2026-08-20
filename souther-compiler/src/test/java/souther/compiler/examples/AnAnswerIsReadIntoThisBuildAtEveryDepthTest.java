package souther.compiler.examples;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Sig;
import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * What a behavior answers is read into this build's classes wherever a declared type stands in it.
 *
 * <p>The emitted check a bound answer is held to guards each rule with an {@code instanceof} against
 * the class this compile emitted, so a value that did not come over matches no guard and every rule
 * is skipped — the check runs and says nothing. Bringing the answer over is what makes it decide,
 * and it has to reach the same depth a declared type does: an answer that is a bare collection is
 * one whose elements are the declared types, and reading the collection without reading them would
 * leave the guard looking at the other build's classes one level in.
 *
 * <p>Held on the crossing rather than through a clause, because the crossing is what was written and
 * what a clause may say is a separate question. The shape is the compiler's own answer to what the
 * behavior answers ({@code Sig.out()}), so what is exercised here is what a run exercises.
 */
class AnAnswerIsReadIntoThisBuildAtEveryDepthTest {

    private static final String MODEL = """
            module example.depth

            data TodoId = Int
            data Todo = { id: TodoId, done: Bool }

            behavior siblingsOf : (id: TodoId) -> List<TodoId>
            behavior oneOf : (id: TodoId) -> Todo
            behavior countOf : (id: TodoId) -> Int
            """;

    /** A collection's elements are read, not just the collection. */
    @Test
    void anElementOfACollectionIsRead() {
        Read read = read();

        Object crossed = read.crossing.crossed(read.sig("siblingsOf").out(), List.of(1L));

        List<?> elements = assertInstanceOf(List.class, crossed);
        assertEquals(1, elements.size());
        assertSame(read.loaded("example.depth.TodoId"), elements.get(0).getClass(),
                "the element is this build's class, which is what an emitted guard tests for");
    }

    /** A declared type standing on its own is read the same way. */
    @Test
    void aNominalAnswerIsRead() {
        Read read = read();

        Object crossed = read.crossing.crossed(read.sig("oneOf").out(),
                Map.of("id", 1L, "done", false));

        assertSame(read.loaded("example.depth.Todo"), crossed.getClass());
    }

    /** A scalar crosses as itself: what a neutral form holds for one is what a guard tests. */
    @Test
    void aScalarAnswerCrossesAsItself() {
        Read read = read();

        assertEquals(3L, read.crossing.crossed(read.sig("countOf").out(), 3L));
    }

    private record Read(Crossing crossing, MemoryClassLoader loader, Map<String, Sig> sigs) {

        Sig sig(String behavior) {
            return sigs.get(behavior);
        }

        Class<?> loaded(String name) {
            try {
                return loader.loadClass(name);
            } catch (ClassNotFoundException e) {
                throw new IllegalStateException(e);
            }
        }
    }

    private static Read read() {
        Compilation c = Compilation.ofSource(MODEL, "Main");
        Map<String, byte[]> classes = c.db().ask(new Output.All()).value();
        assertEquals(List.of(), c.diagnostics().values().stream().flatMap(List::stream)
                .map(d -> String.valueOf(d.diagnostic().code())).toList());
        MemoryClassLoader loader =
                new MemoryClassLoader(classes, AnAnswerIsReadIntoThisBuildAtEveryDepthTest.class
                        .getClassLoader());
        return new Read(new Crossing(loader), loader,
                c.db().ask(new Bodies.Signatures(c.modules().get(0))).value());
    }
}
