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
import java.util.Map;

/**
 * {@code souther mcp}: the doc/api/japi answers, served over the Model Context Protocol's stdio
 * transport — newline-delimited JSON-RPC 2.0. A tool call runs the same code the subcommand runs
 * and hands its text back as the tool result; a failed lookup is the tool's error
 * ({@code isError}), not a protocol error, which is reserved for requests the server cannot read
 * at all.
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

    /** name → its description and input schema; order is the order tools/list answers with. */
    private static final List<Tool> TOOLS = List.of(
            new Tool("doc_search",
                    "Search the Souther language specification and every bundled library doc for a term.",
                    Map.of("term", "the word or phrase to look for"), List.of("term")),
            new Tool("doc_read",
                    "Read one specification section by its anchor (e.g. `newtype`) or one bundled library"
                            + " doc topic by its set-qualified name (e.g. `raoh/tutorial`)."
                            + " `doc_search` and the no-argument `souther doc` listing name them.",
                    Map.of("name", "a section anchor or a set/topic name"), List.of("name")),
            new Tool("stdlib_api",
                    "The Souther standard library's published surface with resolved signatures."
                            + " No name lists everything; a module qualifier (`List`) or a qualified name"
                            + " (`List.map`) narrows the answer.",
                    Map.of("name", "a stdlib module or Module.name, omit for all"), List.of()),
            new Tool("jar_api",
                    "A dependency jar's public API read from its class files, with javadoc from the"
                            + " -sources.jar beside it. Give a fully qualified class or package name.",
                    Map.of("name", "a fully qualified class or package name",
                            "classpath", "jars or class directories to search, path-separated;"
                                    + " omit to search the CLI's own class path"), List.of("name")));

    private record Tool(String name, String description, Map<String, String> params, List<String> required) {}

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
            tool.params().forEach((name, description) -> {
                ObjectNode p = properties.putObject(name);
                p.put("type", "string");
                p.put("description", description);
            });
            var required = schema.putArray("required");
            tool.required().forEach(required::add);
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
        for (String required : tool.required()) {
            JsonNode value = arguments == null ? null : arguments.get(required);
            if (value == null || value.isNull()) {
                return "`" + name + "` needs `" + required + "`";
            }
            if (!value.isString()) {
                return "`" + required + "` must be a string";
            }
            if (value.asString().isBlank()) {
                return "`" + required + "` must not be empty";
            }
        }
        if (arguments != null) {
            for (String given : tool.params().keySet()) {
                JsonNode value = arguments.get(given);
                if (value != null && !value.isNull() && !value.isString()) {
                    return "`" + given + "` must be a string";
                }
            }
        }
        return null;
    }

    private static ObjectNode call(JsonNode params) {
        String tool = params == null || params.get("name") == null ? "" : params.get("name").asString();
        JsonNode arguments = params == null ? null : params.get("params") != null
                ? params.get("params") : params.get("arguments");
        ByteArrayOutputStream captured = new ByteArrayOutputStream();
        PrintStream stream = new PrintStream(captured, true, StandardCharsets.UTF_8);
        int code = switch (tool) {
            case "doc_search" -> DocCommand.run(new String[]{"--search", argument(arguments, "term")}, stream, stream);
            case "doc_read" -> DocCommand.run(new String[]{argument(arguments, "name")}, stream, stream);
            case "stdlib_api" -> {
                String name = argument(arguments, "name");
                yield ApiCommand.run(name.isEmpty() ? new String[]{} : new String[]{name}, stream, stream);
            }
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
        return arguments == null || arguments.get(name) == null ? "" : arguments.get(name).asString();
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
