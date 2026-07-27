package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A newtype may wrap a collection: {@code data Tags = List<String>}. The base is written the way a
 * type is written anywhere else, and the newtype keeps the bare external representation of what it
 * wraps — a JSON array, not {@code {"value": [...]}}. A base with no external representation (a
 * tuple, a function type, an optional) is refused where it is written.
 */
class CompileNewtypeCollectionTest {

    private BytesClassLoader load(String src) {
        return new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
    }

    private Object apply(BytesClassLoader loader, String cls, Object in) throws Exception {
        Object b = loader.loadClass("demo." + cls + "$Impl").getConstructor().newInstance();
        return Codecs.apply(b, in);
    }

    @Test
    void listNewtypeRoundTripsBare() throws Exception {
        BytesClassLoader loader = load("""
                module demo
                data Tags = List<String>
                """);

        Object v = Codecs.decoded(loader, "demo.Tags", List.of("a", "b"));
        assertEquals("demo.Tags", v.getClass().getName());
        assertEquals(List.of("a", "b"), Codecs.encode(loader, "demo.Tags", v),
                "the newtype reads and writes the list's representation, not `{value: [...]}`");
    }

    @Test
    void setNewtypeRoundTripsBare() throws Exception {
        BytesClassLoader loader = load("""
                module demo
                data Labels = Set<String>
                """);

        Object v = Codecs.decoded(loader, "demo.Labels", List.of("a", "b", "a"));
        Object out = Codecs.encode(loader, "demo.Labels", v);
        // a set crosses as a JSON array, so the encoded form is a list; only its membership is fixed
        assertEquals(Set.of("a", "b"), Set.copyOf((List<?>) out));
        assertEquals(2, ((List<?>) out).size(), "the duplicate is dropped on the way in");
    }

    @Test
    void mapNewtypeRoundTripsBare() throws Exception {
        BytesClassLoader loader = load("""
                module demo
                data Stock = Map<String, Int>
                """);

        Object v = Codecs.decoded(loader, "demo.Stock", Map.of("a", 3L));
        assertEquals(Map.of("a", 3L), Codecs.encode(loader, "demo.Stock", v));
    }

    @Test
    void newtypeOverAListOfNamedData() throws Exception {
        // the element carries its own codec, so the newtype writes an array of the element's objects
        BytesClassLoader loader = load("""
                module demo
                data Line = { sku: String, qty: Int }
                data Lines = List<Line>
                """);

        Object v = Codecs.decoded(loader, "demo.Lines", List.of(Map.of("sku", "s-1", "qty", 2L)));
        assertEquals(List.of(Map.of("sku", "s-1", "qty", 2L)), Codecs.encode(loader, "demo.Lines", v));
    }

    @Test
    void collectionNewtypeCarriesAnInvariant() throws Exception {
        BytesClassLoader loader = load("""
                module demo
                import List ( isEmpty )
                data Tags = List<String>
                    invariant isEmpty(value) == false
                """);

        assertEquals(List.of("a"), Codecs.encode(loader, "demo.Tags",
                Codecs.decoded(loader, "demo.Tags", List.of("a"))));
        assertEquals("Err", Codecs.decode(loader, "demo.Tags", List.of()).getClass().getSimpleName(),
                "an empty list breaks the invariant, so the decode fails at the boundary");
    }

    @Test
    void valueOpensTheWrappedCollection() throws Exception {
        BytesClassLoader loader = load("""
                module demo
                import List ( length )
                data Tags = List<String>

                behavior countTags : (t: Tags) -> Int
                let countTags (t) = length(t.value)
                """);

        assertEquals(2L, apply(loader, "CountTags", Codecs.decoded(loader, "demo.Tags", List.of("a", "b"))));
    }

    @Test
    void aCollectionNewtypeIsAMatchableSumCase() throws Exception {
        // a sum case may be a newtype over a collection, and the constructor pattern opens it
        BytesClassLoader loader = load("""
                module demo
                import List ( length )
                data Tags = List<String>
                data Untagged
                data Labelling = Tags | Untagged

                behavior countTags : (l: Labelling) -> Int
                let countTags (l) = match l with
                    | Tags(xs) -> length(xs)
                    | Untagged -> 0
                """);

        Object tagged = Codecs.decoded(loader, "demo.Labelling",
                Map.of("type", "Tags", "value", List.of("a", "b")));
        assertEquals(2L, apply(loader, "CountTags", tagged));
        assertEquals(0L, apply(loader, "CountTags",
                Codecs.decoded(loader, "demo.Labelling", Map.of("type", "Untagged"))));
    }

    @Test
    void aCollectionNewtypeIsNotOrdered() {
        // ordering needs an ordered base; a list is not one, so `<` has nothing to compare
        String src = """
                module demo
                data Tags = List<String>

                behavior before : (a: Tags, b: Tags) -> Bool
                let before (a, b) = a < b
                """;
        assertThrows(CompileException.class, () -> Compiler.compile(src));
    }

    @Test
    void aTupleBaseIsRejected() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Pair = (String, Int)
                """));
        assertEquals("parse.newtype.tuple", e.diagnostic().messageKey(), e.getMessage());
    }

    @Test
    void aFunctionTypeBaseIsRejected() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Rule = (String) -> Bool
                """));
        assertEquals("parse.newtype.fntype", e.diagnostic().messageKey(), e.getMessage());
    }

    @Test
    void anOptionBaseIsRejected() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Note = Option<String>
                """));
        assertEquals("check.newtype.optional", e.diagnostic().messageKey(), e.getMessage());
    }

    @Test
    void anOptionalMarkOnTheBaseIsRejected() {
        // `?` says the use site may omit the value; it is written on the field, not on the type
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Note = String?
                """));
        assertEquals("check.newtype.optional", e.diagnostic().messageKey(), e.getMessage());
    }

    @Test
    void theOptionalComplaintNamesTheNewtypeAndPointsAtTheField() {
        // both spellings reach the same report, because it is read off the resolved type rather
        // than off the word that was written
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Note = String?
                """));
        assertTrue(e.getMessage().contains("Note"), e.getMessage());
        assertFalse(e.getMessage().contains("`value`") || e.getMessage().contains("Note.value"),
                "the author never wrote a field called `value`: " + e.getMessage());
    }

    @Test
    void aGenericSumCaseIsRejected() {
        // a sum case is a reference to a declared named data, so it is never a generic type
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data B
                data X = List<String> | B
                """));
        assertEquals("parse.sum.case.generic", e.diagnostic().messageKey(), e.getMessage());
    }

    @Test
    void aMapNewtypeKeyedOffTheBoundaryIsRejected() {
        // a JSON object's keys are strings, so an Int-keyed map cannot cross as itself
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo
                data Stock = Map<Int, Int>
                """));
        assertEquals("check.map.key.field", e.diagnostic().messageKey(), e.getMessage());
        assertTrue(e.getMessage().contains("`Stock`") && !e.getMessage().contains("Stock.value"),
                "the complaint names the newtype, not a field the author never wrote: " + e.getMessage());
    }

    @Test
    void anExampleFixtureConstructsAListNewtype() {
        // the fixture is written as the constructor applied to the collection literal
        Compiler.compile("""
                module demo
                import List ( length )
                data Tags = List<String>

                behavior countTags : (t: Tags) -> Int
                let countTags (t) = length(t.value)

                example countTags
                  | (Tags(["a", "b"])) -> 2
                """);
    }

    @Test
    void anExampleFixtureConstructsAMapNewtype() {
        // the argument is shaped against the newtype's own base, so a list of pairs becomes a Map
        Compiler.compile("""
                module demo
                import Map ( size )
                data Stock = Map<String, Int>

                behavior lineCount : (s: Stock) -> Int
                let lineCount (s) = size(s.value)

                example lineCount
                  | (Stock([("a", 3), ("b", 1)])) -> 2
                """);
    }
}
