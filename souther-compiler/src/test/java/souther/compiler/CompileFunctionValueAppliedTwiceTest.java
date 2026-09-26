package souther.compiler;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A value answering a function, applied twice in one body. Each application is the value applied,
 * so two of them are two applications and not one value named twice.
 */
class CompileFunctionValueAppliedTwiceTest {

    private static final String ADDER = """
            let adder (n: Int) = (x) -> x + n
            """;

    @Test
    void twoApplicationsAreSummed() throws Exception {
        assertEquals(84L, answered("""
                let inc = adder(1)
                """, "Count(inc(c.value) + inc(c.value))", 41L));
    }

    @Test
    void anApplicationOfAnApplicationIsApplied() throws Exception {
        assertEquals(43L, answered("""
                let inc = adder(1)
                """, "Count(inc(inc(c.value)))", 41L));
    }

    @Test
    void twoApplicationsInBranchesAreApplied() throws Exception {
        assertEquals(43L, answered("""
                let inc = adder(1)
                """, "if c.value > 0 then Count(inc(c.value)) else Count(inc(c.value + 1))", 42L));
    }

    @Test
    void aValueWithTheTypeWrittenIsAppliedTheSame() throws Exception {
        assertEquals(84L, answered("""
                let inc: (Int) -> Int = adder(1)
                """, "Count(inc(c.value) + inc(c.value))", 41L));
    }

    @Test
    void aValueBodyThatNamesAValueTwiceIsAppliedTwice() throws Exception {
        assertEquals(52L, answered("""
                let base = List.length([1, 2, 3])
                let inc = adder(base)
                let twice (x: Int) = inc(x) + inc(x)
                """, "Count(twice(c.value) + twice(c.value))", 10L));
    }

    @Test
    void aValueWithABranchInItsBodyIsAppliedTwice() throws Exception {
        assertEquals(24L, answered("""
                let pick = if List.length([1, 2]) > 1 then adder(1) else adder(2)
                """, "Count(pick(c.value) + pick(c.value))", 11L));
    }

    @Test
    void twoApplicationsThroughALocalNameAreApplied() throws Exception {
        assertEquals(84L, answered("""
                let inc = adder(1)
                """, "{ let g = inc\n Count(g(c.value) + g(c.value)) }", 41L));
    }

    @Test
    void applicationsInAHelperCalledTwiceAreApplied() throws Exception {
        assertEquals(88L, answered("""
                let inc = adder(1)
                let both (y: Int) = inc(y) + inc(y)
                """, "Count(both(c.value) + both(c.value))", 21L));
    }

    @Test
    void aValueHandedToAnOperationAndAppliedIsApplied() throws Exception {
        assertEquals(3L, answered("""
                let inc = adder(1)
                """, "Count(List.length(List.map((y) -> inc(y), [c.value, inc(c.value)])) + inc(0))", 1L));
    }

    @Test
    void twoApplicationsAreAcceptedWithNoOneToRunThem() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module shop exposing ( use )

                %s
                let inc = adder(1)

                behavior use : (n: Int) -> Int
                let use (n) = inc(n) + inc(n)
                """.formatted(ADDER)));
    }

    /** What `use` answers for {@code input}, with {@code values} declared beside it. */
    private long answered(String values, String result, long input) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module shop exposing ( Count, use )

                data Count = Int

                %s
                %s
                behavior use : (c: Count) -> Count constructs Count
                let use (c) = %s
                """.formatted(ADDER, values, result)), getClass().getClassLoader());
        Object behavior = Emitted.behavior(loader, "shop", "use").getDeclaredConstructor().newInstance();
        Object in = Codecs.decoded(loader, "shop.Count", input);

        return (long) Codecs.encode(loader, "shop.Count", Codecs.apply(behavior, in));
    }
}
