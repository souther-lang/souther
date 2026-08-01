package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

class ScratchTupleLoopTest {

    private static final String MODULE = """
            module demo

            data Req = { m: Map<String, Int>, s: Set<Int>, xs: List<Int> }
            data Out = { n: Int }

            behavior go : (r: Req) -> Out
                constructs Out
            let go (r) = Out { n = Map.size(r.m) }
            """;

    @Test
    void whatClassesDoDecodedCollectionsArriveAs() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(MODULE), getClass().getClassLoader());
        Map<String, Object> inner = new LinkedHashMap<>();
        inner.put("a", 1L);
        Map<String, Object> raw = new LinkedHashMap<>();
        raw.put("m", inner);
        raw.put("s", List.of(1L, 2L));
        raw.put("xs", List.of(1L, 2L));
        Object req = Codecs.decoded(loader, "demo.Req", raw);
        for (String f : new String[] {"m", "s", "xs"}) {
            Object v = req.getClass().getMethod(f).invoke(req);
            System.out.println("FIELD " + f + " -> " + v.getClass().getName());
        }
    }
}
