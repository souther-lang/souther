package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.runtime.Result;
import souther.runtime.boundary.Path.Segment;
import souther.runtime.boundary.Refusal;
import souther.runtime.boundary.Refusals;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What a refusal hands a reporter is read off the refusal itself, not off a decoder binding that may
 * write less of it (spec {@code [#decoder-error]}, {@code [#what-an-invariant-refusal-says]}).
 *
 * <p>A JSON Pointer writes the element at index 0 and the member named {@code 0} alike, and a library
 * whose paths tell them apart can only report what it is handed. A constraint's data is ordered, so
 * a library whose messages place arguments by position can report a constraint it does not know.
 */
class ARefusalSaysEachStepAndItsDataAsTheyAreTest {

    private static final String MODULE = """
            module demo

            data Code = String
                invariant String.length(value) >= 3
            data InAList = { a: List<Code> }
            data InAMap = { a: Map<String, Code> }
            """;

    private static Refusal refusalOf(ClassLoader loader, String type, Object raw) throws Exception {
        Result<?, Refusals> read = Codecs.derived(loader, "demo." + type).decode(raw);
        Refusals refusals = (Refusals) assertInstanceOf(Result.Err.class, read).error();
        assertEquals(1, refusals.asList().size(), refusals.toString());
        return refusals.asList().get(0);
    }

    @Test
    void anElementAndAMemberWrittenAlikeAreTwoStepsAndADataKeepsItsOrder() throws Exception {
        ClassLoader loader = new BytesClassLoader(Compiler.compile(MODULE), getClass().getClassLoader());

        Refusal element = refusalOf(loader, "InAList", Map.of("a", List.of("ab")));
        Refusal member = refusalOf(loader, "InAMap", Map.of("a", Map.of("0", "ab")));

        assertEquals("/a/0", element.path().toJsonPointer());
        assertEquals("/a/0", member.path().toJsonPointer());
        assertEquals(List.of(new Segment.Member("a"), new Segment.Element(0)), element.path().segments());
        assertEquals(List.of(new Segment.Member("a"), new Segment.Member("0")), member.path().segments());

        Refusal.Constraint shorter = assertInstanceOf(Refusal.Constraint.class, element);
        assertEquals("minLength", shorter.name());
        assertEquals(List.of("min", "actual"), List.copyOf(shorter.data().keySet()));
        assertEquals(List.of(3, 2), List.copyOf(shorter.data().values()));
    }
}
