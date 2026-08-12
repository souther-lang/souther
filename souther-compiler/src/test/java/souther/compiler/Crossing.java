package souther.compiler;

import souther.compiler.ast.Ast;
import souther.compiler.check.Sig;
import souther.compiler.query.Compilation;

import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * One behavior driven across the JSON boundary the way {@code souther run} drives it, without the
 * command line around it: compile the source, read the sole input, apply, and write the answer back.
 *
 * <p>What the boundary reads and writes is asked of {@link JsonBoundary} rather than of the CLI,
 * because these are claims about the reading — which has two other implementations it has to agree
 * with, both in this module — and not about the command that happens to reach it. The argument
 * vector, the exit code and the wording of a failure are the CLI's, and are tested where they live.
 */
final class Crossing {

    private Crossing() {}

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** The behavior's answer as JSON, for a sole input that reads. */
    static String of(String source, String module, String behavior, String json) throws Exception {
        Compilation compilation = Compiler.compiled(source, module, new ArrayList<>());
        Ast.Module written = compilation.module(compilation.modules().get(0));
        Sig sig = compilation.signatures(written.name()).get(behavior);

        // One loader for the whole crossing, as `souther run` holds one: asked twice, a compilation
        // answers with two, and a value the first one's classes made is not a value the second one's
        // classes are — a decoded key stops equalling the key the behavior looks up.
        ClassLoader loader = compilation.loader();
        JsonBoundary.Read read = JsonBoundary.read(loader, sig.ins().get(0), JSON.readTree(json));
        Object argument = assertInstanceOf(JsonBoundary.Read.Value.class, read, json).value();
        Object result = JsonBoundary.apply(loader, written.name(), behavior,
                new Object[] {argument});
        return JSON.writeValueAsString(
                JsonBoundary.write(loader, written.name(), behavior, sig.out(), result));
    }

    /** What reading {@code json} as the behavior's sole input came to. */
    static JsonBoundary.Read reading(String source, String module, String behavior, String json)
            throws Exception {
        Compilation compilation = Compiler.compiled(source, module, new ArrayList<>());
        Ast.Module written = compilation.module(compilation.modules().get(0));
        Sig sig = compilation.signatures(written.name()).get(behavior);
        return JsonBoundary.read(compilation.loader(), sig.ins().get(0), JSON.readTree(json));
    }

    /** The refusal reading {@code json} came to, for a test that is about the refusal. */
    static JsonBoundary.Read.Refused refusalOf(String source, String module, String behavior,
                                               String json) throws Exception {
        return assertInstanceOf(JsonBoundary.Read.Refused.class,
                reading(source, module, behavior, json), json);
    }

    /** The issues' messages, in the order they were found. */
    static java.util.List<String> messagesOf(JsonBoundary.Read.Refused refused) {
        return refused.issues().asList().stream().map(net.unit8.raoh.Issue::message).toList();
    }

    /** The JSON pointers the issues stand at, in the order they were found. */
    static java.util.List<String> pointersOf(JsonBoundary.Read.Refused refused) {
        return refused.issues().asList().stream().map(i -> i.path().toJsonPointer()).toList();
    }
}
