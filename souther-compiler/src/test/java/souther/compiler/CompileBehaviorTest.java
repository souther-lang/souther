package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/** End-to-end test for pure single-input behaviors and the constructs checks (spec §behavior, §e1002, §e1006). */
class CompileBehaviorTest {

    private static final String MODULE = """
            module demo

            data MemberId = String

            data Member = {
                id: MemberId
                , name: String
            }

            data Response = { id: MemberId }

            behavior toResponse : (m: Member) -> Response
                constructs Response

            let toResponse (m) = Response { id = m.id }
            """;

    @Test
    void pureBehaviorTransformsAValue() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(MODULE), getClass().getClassLoader());

        Object member = Codecs.decoded(loader, "demo.Member", Map.of("id", "m-1", "name", "bob"));

        Object behavior = Emitted.behavior(loader, "demo", "toResponse").getConstructor().newInstance();
        Object response = Codecs.apply(behavior, member);

        Map<?, ?> encoded = (Map<?, ?>) Codecs.encode(loader, "demo.Response", response);
        assertEquals("m-1", encoded.get("id"), "response carries the member id");
    }

    @Test
    void undeclaredConstructionIsE1002() {
        // `constructs` may be omitted (then inferred), but a declared clause must be complete: here
        // `Empty` is declared while `Response` is also built, so the undeclared `Response` is E1002.
        String src = """
                module demo
                data Response = { id: String }
                data Note = { s: String }
                behavior make : (x: String) -> Response | Note
                    constructs Note

                let make (x) = if x == "" then Note { s = x } else Response { id = x }
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E1002", e.code());
    }
}
