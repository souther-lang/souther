package souther.compiler.doc;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import tools.jackson.databind.node.ObjectNode;

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.List;

/**
 * {@code souther mcp}: the doc/api/japi answers, served over the Model Context Protocol's stdio
 * transport — newline-delimited JSON-RPC 2.0. A tool call runs the same code the subcommand runs
 * and hands its text back as the tool result; a failed lookup is the tool's error
 * ({@code isError}), not a protocol error, which is reserved for requests the server cannot read
 * at all.
 *
 * <p>What the tools publish is what the commands can do, not the shapes their argument vectors
 * happen to take. A client here has no shell to fall back to and no listing of the commands it is
 * reaching, so a capability with no spelling in this table is one it can only arrive at by
 * guessing. Where the two do differ — {@code stdlib_api_search} takes no count because the stdlib
 * surface is answered whole — the tool's own description says so.
 *
 * <p>Stdout carries protocol lines only; everything a command would say lands inside a response.
 */
public final class McpServer {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * The protocol revisions this server answers under, newest first.
     *
     * <p>These are the revisions whose opening exchange is {@code initialize} and whose requests
     * carry their arguments where this server looks for them. What it serves is the same under both,
     * so a client on either is answered on its own.
     *
     * <p>The 2026 revisions are deliberately absent. They settle the connection's era in the opening
     * exchange and carry each request's identity in an envelope this server neither reads nor
     * writes; answering {@code initialize} with one of them would claim an era it does not speak.
     * A client that can only talk that way should fail to connect rather than be told it succeeded.
     */
    private static final List<String> PROTOCOL_VERSIONS = List.of("2025-11-25", "2025-06-18");

    /** The tools this server publishes, in the order {@code tools/list} answers with. */
    private static final List<Tool> TOOLS = List.of(
            new Tool("doc_search",
                    "Search the Souther language specification and every bundled library doc for a term."
                            + " Answers the 20 best hits unless `limit` says otherwise.",
                    List.of(new Param("term", Kind.STRING, true, "the word or phrase to look for"),
                            new Param("limit", Kind.INTEGER, false,
                                    "how many hits to answer with; 0 for all of them (default 20)"))),
            new Tool("doc_read",
                    "Read the Souther specification and the docs bundled libraries ship. With no `name`"
                            + " it lists every section anchor and every shipped topic as `name<TAB>title`,"
                            + " one per line — start there. With a `name` it reads that one specification"
                            + " section by its anchor (e.g. `newtype`) or that one library topic by its"
                            + " set-qualified name (e.g. `raoh/tutorial`).",
                    List.of(new Param("name", Kind.STRING, false,
                            "a section anchor or a set/topic name; omit to list every one of them"))),
            new Tool("stdlib_api",
                    "The Souther standard library's published surface with resolved signatures. No name"
                            + " lists everything; a module qualifier (`List`) or a qualified name"
                            + " (`List.map`) narrows the answer. With `source` and a module name it reads"
                            + " that module's own source instead, whose comments say what each"
                            + " declaration means.",
                    List.of(new Param("name", Kind.STRING, false,
                                    "a stdlib module or Module.name, omit for all"),
                            new Param("source", Kind.BOOLEAN, false,
                                    "read the named module's own source rather than its signatures"))),
            new Tool("stdlib_api_search",
                    "Find published stdlib names containing a term. Answers every match — the surface is"
                            + " small enough that nothing is ever held back.",
                    List.of(new Param("term", Kind.STRING, true,
                            "a piece of the name to look for, matched without regard to case"))),
            new Tool("jar_api",
                    "A dependency jar's public API read from its class files, with javadoc from the"
                            + " -sources.jar beside it. Give a fully qualified class or package name.",
                    List.of(new Param("name", Kind.STRING, true,
                                    "a fully qualified class or package name"),
                            new Param("classpath", Kind.STRING, false,
                                    "jars or class directories to search, path-separated;"
                                            + " omit to search the CLI's own class path"))));

    /** What a declared argument may hold, and the JSON Schema type that says so. */
    private enum Kind {
        STRING("string"), INTEGER("integer"), BOOLEAN("boolean");

        private final String schemaType;

        Kind(String schemaType) {
            this.schemaType = schemaType;
        }
    }

    private record Param(String name, Kind kind, boolean required, String description) {}

    private record Tool(String name, String description, List<Param> params) {

        Param param(String name) {
            return params.stream().filter(p -> p.name().equals(name)).findFirst().orElse(null);
        }
    }

    private McpServer() {}

    public static int serve(InputStream in, OutputStream out) {
        BufferedReader reader = new BufferedReader(new InputStreamReader(in, StandardCharsets.UTF_8));
        PrintWriter writer = new PrintWriter(out, true, StandardCharsets.UTF_8);
        try {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.isBlank()) {
                    continue;
                }
                JsonNode request;
                try {
                    request = JSON.readTree(line);
                } catch (RuntimeException e) {
                    writer.println(JSON.writeValueAsString(error(null, -32700, "parse error")));
                    continue;
                }
                JsonNode id = request.get("id");
                if (id == null) {
                    continue; // A notification expects silence, whatever its method.
                }
                writer.println(JSON.writeValueAsString(respond(request, id)));
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        return 0;
    }

    private static ObjectNode respond(JsonNode request, JsonNode id) {
        String method = request.get("method") == null ? "" : request.get("method").asString();
        return switch (method) {
            case "initialize" -> result(id, initializeResult(request.get("params")));
            case "ping" -> result(id, JSON.createObjectNode());
            case "tools/list" -> result(id, toolsResult());
            // A tool that blows up is this call's failure, not the session's: the server is long
            // lived and a client that mistypes an argument must not lose the ones after it.
            case "tools/call" -> {
                String invalid = invalidArguments(request.get("params"));
                if (invalid != null) {
                    yield error(id, -32602, invalid);
                }
                try {
                    yield result(id, call(request.get("params")));
                } catch (RuntimeException e) {
                    yield result(id, failed(e.getClass().getSimpleName()
                            + (e.getMessage() == null ? "" : ": " + e.getMessage())));
                }
            }
            default -> error(id, -32601, "method not found: " + method);
        };
    }

    private static ObjectNode initializeResult(JsonNode params) {
        JsonNode asked = params == null ? null : params.get("protocolVersion");
        String version = asked != null && asked.isString() && PROTOCOL_VERSIONS.contains(asked.asString())
                ? asked.asString()
                : PROTOCOL_VERSIONS.getFirst();
        ObjectNode result = JSON.createObjectNode();
        result.put("protocolVersion", version);
        result.putObject("capabilities").putObject("tools");
        ObjectNode server = result.putObject("serverInfo");
        server.put("name", "souther");
        String built = McpServer.class.getPackage().getImplementationVersion();
        server.put("version", built == null ? "dev" : built);
        return result;
    }

    private static ObjectNode toolsResult() {
        ObjectNode result = JSON.createObjectNode();
        var tools = result.putArray("tools");
        for (Tool tool : TOOLS) {
            ObjectNode t = tools.addObject();
            t.put("name", tool.name());
            t.put("description", tool.description());
            ObjectNode schema = t.putObject("inputSchema");
            schema.put("type", "object");
            ObjectNode properties = schema.putObject("properties");
            for (Param param : tool.params()) {
                ObjectNode p = properties.putObject(param.name());
                p.put("type", param.kind().schemaType);
                p.put("description", param.description());
            }
            var required = schema.putArray("required");
            tool.params().stream().filter(Param::required).map(Param::name).forEach(required::add);
            // An argument this server would drop is one a client can spend a call learning about,
            // so the schema says up front that there are no others to guess at.
            schema.put("additionalProperties", false);
        }
        return result;
    }

    /**
     * What is wrong with a call's arguments, or null when nothing is.
     *
     * <p>The arguments arrive from a client and are checked against the tool's own schema before
     * anything runs. An argument that is absent, of another type, or a string of no characters is
     * not a value to be worked with — the search term this matters most for matches everything and
     * at every position, and the walk over its occurrences would not advance. Reporting it as an
     * invalid parameter says the tool was never entered, which a tool error would not.
     *
     * <p>An argument the schema does not declare is refused for the same reason rather than
     * dropped. A client that guesses a name — and one that has only these tools to work with will
     * guess — would otherwise be handed an answer computed without it, with nothing in the answer
     * saying the argument had no effect.
     */
    private static String invalidArguments(JsonNode params) {
        String name = params == null || params.get("name") == null ? "" : params.get("name").asString();
        Tool tool = TOOLS.stream().filter(t -> t.name().equals(name)).findFirst().orElse(null);
        if (tool == null) {
            return "no tool `" + name + "`";
        }
        JsonNode arguments = params.get("arguments");
        // The schema says arguments are an object. A tool that requires none of them would
        // otherwise take anything at all and answer as though it had been called properly.
        if (arguments != null && !arguments.isNull() && !arguments.isObject()) {
            return "`arguments` must be an object";
        }
        if (arguments != null && arguments.isObject()) {
            for (String given : arguments.propertyNames()) {
                if (tool.param(given) == null) {
                    return "`" + name + "` has no argument `" + given + "`; it takes "
                            + String.join(", ", tool.params().stream()
                                    .map(p -> "`" + p.name() + "`").toList());
                }
            }
        }
        for (Param param : tool.params()) {
            JsonNode value = arguments == null ? null : arguments.get(param.name());
            if (value == null || value.isNull()) {
                if (param.required()) {
                    return "`" + name + "` needs `" + param.name() + "`";
                }
                continue;
            }
            String wrong = malformed(param, value);
            if (wrong != null) {
                return wrong;
            }
        }
        // `--source` names a module, and the command it reaches has no listing to fall back on.
        if (flag(arguments, "source") && argument(arguments, "name").isEmpty()) {
            return "`source` needs `name` — the module whose source to read";
        }
        return null;
    }

    /** Why this value does not fit the argument it was given for, or null when it does. */
    private static String malformed(Param param, JsonNode value) {
        return switch (param.kind()) {
            case STRING -> !value.isString()
                    ? "`" + param.name() + "` must be a string"
                    : value.asString().isBlank() ? "`" + param.name() + "` must not be empty" : null;
            // A count written as a string is the shape a client falls into when it is guessing,
            // and answering it with the default count would look like the count was honoured.
            case INTEGER -> value.isIntegralNumber() ? null : "`" + param.name() + "` must be an integer";
            case BOOLEAN -> value.isBoolean() ? null : "`" + param.name() + "` must be true or false";
        };
    }

    /**
     * Runs the call and answers with what the command said.
     *
     * <p>Each tool names a capability, and the arguments it was given decide which of the
     * underlying command's forms carries it out. A tool is not a fixed way of spelling one
     * invocation: {@code doc_read} with no name is the listing that command prints for no
     * arguments, and it is reachable here for the same reason it is reachable at a prompt.
     *
     * <p>The command is told it is answering an MCP client, so that what it offers next is a tool
     * call rather than a shell command the caller has no way to run.
     */
    private static ObjectNode call(JsonNode params) {
        String tool = params == null || params.get("name") == null ? "" : params.get("name").asString();
        JsonNode arguments = params == null ? null : params.get("arguments");
        ByteArrayOutputStream captured = new ByteArrayOutputStream();
        PrintStream stream = new PrintStream(captured, true, StandardCharsets.UTF_8);
        int code = switch (tool) {
            case "doc_search" -> {
                JsonNode limit = arguments == null ? null : arguments.get("limit");
                String[] args = limit == null || limit.isNull()
                        ? new String[]{"--search", argument(arguments, "term")}
                        : new String[]{"--search", argument(arguments, "term"),
                                "--limit", String.valueOf(limit.asInt())};
                yield DocCommand.run(args, stream, stream, Caller.MCP);
            }
            case "doc_read" -> {
                String name = argument(arguments, "name");
                yield DocCommand.run(name.isEmpty() ? new String[]{} : new String[]{name},
                        stream, stream, Caller.MCP);
            }
            case "stdlib_api" -> {
                String name = argument(arguments, "name");
                String[] args = flag(arguments, "source")
                        ? new String[]{"--source", name}
                        : name.isEmpty() ? new String[]{} : new String[]{name};
                yield ApiCommand.run(args, stream, stream, Caller.MCP);
            }
            case "stdlib_api_search" -> ApiCommand.run(
                    new String[]{"--search", argument(arguments, "term")}, stream, stream, Caller.MCP);
            case "jar_api" -> {
                String classpath = argument(arguments, "classpath");
                String[] args = classpath.isEmpty()
                        ? new String[]{argument(arguments, "name")}
                        : new String[]{argument(arguments, "name"), "-cp", classpath};
                yield JapiCommand.run(args, stream, stream);
            }
            default -> {
                stream.println("no tool `" + tool + "`");
                yield 2;
            }
        };
        ObjectNode result = JSON.createObjectNode();
        ObjectNode content = result.putArray("content").addObject();
        content.put("type", "text");
        content.put("text", captured.toString(StandardCharsets.UTF_8));
        result.put("isError", code != 0);
        return result;
    }

    private static ObjectNode failed(String said) {
        ObjectNode result = JSON.createObjectNode();
        ObjectNode content = result.putArray("content").addObject();
        content.put("type", "text");
        content.put("text", said);
        result.put("isError", true);
        return result;
    }

    private static String argument(JsonNode arguments, String name) {
        return arguments == null || arguments.get(name) == null || !arguments.get(name).isString()
                ? "" : arguments.get(name).asString();
    }

    private static boolean flag(JsonNode arguments, String name) {
        JsonNode value = arguments == null ? null : arguments.get(name);
        return value != null && value.isBoolean() && value.asBoolean();
    }

    private static ObjectNode result(JsonNode id, ObjectNode result) {
        ObjectNode response = envelope(id);
        response.set("result", result);
        return response;
    }

    private static ObjectNode error(JsonNode id, int code, String message) {
        ObjectNode response = envelope(id);
        ObjectNode error = response.putObject("error");
        error.put("code", code);
        error.put("message", message);
        return response;
    }

    private static ObjectNode envelope(JsonNode id) {
        ObjectNode response = JSON.createObjectNode();
        response.put("jsonrpc", "2.0");
        if (id == null) {
            response.putNull("id");
        } else {
            response.set("id", id);
        }
        return response;
    }
}
