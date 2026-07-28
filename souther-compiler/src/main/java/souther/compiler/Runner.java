package souther.compiler;

import souther.compiler.check.Symbols;
import souther.compiler.ast.Ast;
import souther.compiler.check.PipelineSigs;
import souther.compiler.check.Resolve;
import souther.compiler.check.Sig;
import souther.compiler.types.Type;
import souther.compiler.check.TypeChecker;
import souther.compiler.diag.Messages;
import souther.compiler.frontend.CstFrontend;

import net.unit8.raoh.Err;
import net.unit8.raoh.Issues;
import net.unit8.raoh.ResourceBundleMessageResolver;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Result;
import net.unit8.raoh.decode.Decoder;
import net.unit8.raoh.json.JsonDecoders;
import net.unit8.raoh.encode.Encoder;
import net.unit8.raoh.encode.ObjectEncoders;

import souther.runtime.Sets;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Drives a compiled behavior from the command line: {@code souther run <file.sou> [--behavior
 * <name>] [--input <json>]}. The runner is itself the Java boundary (spec section 13) — it decodes
 * the JSON input into the behavior's parameter types through their derived decoders, applies the
 * behavior, and encodes the returned domain value back to JSON through its derived encoder. Souther
 * keeps no I/O of its own; a header-less {@code .sou} is named after the file (see {@link Parser}).
 *
 * <p>The runner drives a single self-contained {@code .sou} file: stdlib imports resolve, but it
 * cannot link against other user modules. A behavior is runnable when it has a {@code let} and no
 * {@code requires}, or when it is a {@code >->} pipeline whose stages are all themselves runnable
 * (each has a {@code let} and no {@code requires}) — such a pipeline compiles to a no-arg {@code
 * $Impl} that chains the stages, so it runs like any other behavior. An injected behavior (no
 * implementation), one that needs injected dependencies, or a pipeline with such a stage has nothing
 * for {@code run} to supply; each is refused with a reason.
 */
public final class Runner {

    private Runner() {}

    /**
     * A user-facing failure of {@code souther run}, carrying the process exit code to use.
     *
     * <p>It is written twice, as a compile error is (see {@code Diagnostic}): {@code getMessage()} is
     * the English form a Java caller sees, and {@code messageKey} plus {@code args} resolve against
     * the catalog for the locale the command line selected. The runner is a user surface, so its
     * failures are read in the same language as the compiler's diagnostics.
     */
    static final class RunException extends RuntimeException {
        final int exitCode;
        private final String messageKey;
        private final Object[] args;
        /** The decoder's own issues, when this is a decode failure: their text is written by the
         * decoder's catalog, so it is resolved per locale rather than fixed at throw time. */
        private final Issues issues;

        RunException(String messageKey, String message, int exitCode, Issues issues, Object... args) {
            super(message);
            this.exitCode = exitCode;
            this.messageKey = messageKey;
            this.args = args;
            this.issues = issues;
        }

        RunException(String message) {
            this(null, message, 1, null);
        }

        /** This failure in {@code locale}. An exit code of 2 is a usage error, which ends with the
         * command's usage line. */
        String localized(java.util.Locale locale) {
            if (messageKey == null) {
                return getMessage();
            }
            Object[] resolved = args;
            if (issues != null) {
                // the issue text is the last argument of `run.decode.failed`, the one key that carries
                // issues; rewriting it here is what resolves the decoder's own wording per locale
                resolved = args.clone();
                resolved[resolved.length - 1] = detail(issues.resolve(DECODE_MESSAGES, locale));
            }
            String text = Messages.get(messageKey, locale, resolved);
            return exitCode == 2 ? text + "\n" + Messages.get("run.usage.line", locale) : text;
        }
    }

    /** The decoder's own message catalog, which its issues are written against. */
    private static final ResourceBundleMessageResolver DECODE_MESSAGES =
            new ResourceBundleMessageResolver("net.unit8.raoh.messages");

    /** A failure that names a catalog key: the English literal for a Java caller, the key for the
     * command line's chosen locale. */
    private static RunException fail(String key, String message, Object... args) {
        return new RunException(key, message, 1, null, args);
    }

    /** Parses the {@code run} subcommand's arguments (everything after {@code run}) and runs it. */
    static String runCli(String[] args) {
        Path file = null;
        String behaviorName = null;
        String inputJson = null;
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "--behavior" -> behaviorName = value(args, ++i, "--behavior");
                case "--input" -> inputJson = value(args, ++i, "--input");
                default -> {
                    if (args[i].startsWith("--")) {
                        throw usage("run.usage.unknownoption", "unknown option `" + args[i] + "`", args[i]);
                    }
                    if (file != null) {
                        throw usage("run.usage.singlefile", "run takes a single .sou file");
                    }
                    file = Path.of(args[i]);
                }
            }
        }
        if (file == null) {
            throw usage("run.usage.nofile", "no source file given");
        }
        return run(file, behaviorName, inputJson);
    }

    private static String value(String[] args, int i, String option) {
        if (i >= args.length) {
            throw usage("run.usage.optionvalue", "`" + option + "` needs a value", option);
        }
        return args[i];
    }

    private static RunException usage(String key, String problem, Object... args) {
        return new RunException(key, problem
                + "\nusage: souther run <file.sou> [--behavior <name>] [--input <json>]", 2, null, args);
    }

    /** Compiles {@code file}, drives {@code behaviorName} with {@code inputJson}, and returns the
     * encoded output as JSON text. {@code behaviorName} may be null when the module holds exactly
     * one runnable behavior; {@code inputJson} may be null for a zero-argument behavior. */
    public static String run(Path file, String behaviorName, String inputJson) {
        String source = read(file);
        String moduleName = moduleName(file);

        Map<String, byte[]> classes = Compiler.compile(source, moduleName);
        Ast.Module parsed = CstFrontend.parse(source, moduleName);
        Ast.Module module = Resolve.module(parsed, TypeChecker.symbols(parsed));
        Symbols symbols = TypeChecker.symbols(module);
        Map<String, Sig> sigs = PipelineSigs.signatures(module, symbols);

        Ast.BehaviorDef spec = resolveBehavior(module, behaviorName);
        Sig sig = sigs.get(spec.name());
        List<Type> ins = sig.ins();

        JsonNode[] rawArgs = splitInput(spec.name(), ins.size(), inputJson);
        MemoryClassLoader loader = new MemoryClassLoader(classes, Runner.class.getClassLoader());
        Object[] args = new Object[ins.size()];
        for (int i = 0; i < ins.size(); i++) {
            args[i] = decode(loader, module.name(), ins.get(i), rawArgs[i], i);
        }

        Object result = invoke(loader, module.name(), spec.name(), args);
        Object encoded = encode(module.name(), sig.out(), result);
        return writeJson(encoded);
    }

    // --- behavior selection ---------------------------------------------------------------------

    private static Ast.BehaviorDef resolveBehavior(Ast.Module module, String requested) {
        java.util.Set<String> implemented = module.fns().stream()
                .map(Ast.FnDef::name).collect(Collectors.toSet());
        Map<String, List<String>> pipeStages = PipelineSigs.pipelineStages(module);
        Map<String, Ast.BehaviorDef> runnable = new java.util.LinkedHashMap<>();
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (b instanceof Ast.SpecBehavior spec
                    && implemented.contains(spec.name()) && spec.requires().isEmpty()) {
                runnable.put(spec.name(), spec);
            } else if (b instanceof Ast.PipeBehavior pipe
                    && pipelineBlocker(module, pipe, implemented, pipeStages) == null) {
                runnable.put(pipe.name(), pipe);
            }
        }
        if (requested == null) {
            if (runnable.size() == 1) {
                return runnable.values().iterator().next();
            }
            if (runnable.isEmpty()) {
                throw fail("run.behavior.none", "no runnable behavior in this module. "
                        + "A runnable behavior has a `let` and no `requires`.");
            }
            String names = String.join(", ", runnable.keySet());
            throw usage("run.behavior.several",
                    "several runnable behaviors — pick one with --behavior: " + names, names);
        }
        Ast.BehaviorDef found = runnable.get(requested);
        if (found != null) {
            return found;
        }
        throw whyNotRunnable(module, requested, runnable.keySet());
    }

    /** A reason a behavior cannot be driven, in both forms: the catalog key with its arguments, and
     * the English literal. The list of behaviors that can be driven is appended to both. */
    private record Blocker(String key, String message, Object... args) {}

    /**
     * Why a {@code >->} pipeline cannot be driven by {@code run}, or null when every stage is
     * in-language. A pipeline whose flattened stages all have a {@code let} and no {@code requires}
     * compiles to an {@code $Impl} with a public no-arg constructor, so it runs exactly like a simple
     * behavior. A stage with no implementation (injected from Java) or one that needs its own injected
     * dependencies would make that constructor take those behaviors, which {@code run} cannot supply.
     */
    private static Blocker pipelineBlocker(Ast.Module module, Ast.PipeBehavior pipe,
            java.util.Set<String> implemented, Map<String, List<String>> pipeStages) {
        Map<String, Ast.SpecBehavior> specs = new java.util.HashMap<>();
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (b instanceof Ast.SpecBehavior spec) {
                specs.put(spec.name(), spec);
            }
        }
        for (String stage : PipelineSigs.flattenStages(pipe.stages(), pipeStages, pipe.pos())) {
            if (!implemented.contains(stage)) {
                return new Blocker("run.pipeline.noimpl",
                        "`" + pipe.name() + "` is a pipeline whose stage `" + stage
                                + "` has no implementation (it is injected from Java), which `run` cannot supply.",
                        pipe.name(), stage);
            }
            Ast.SpecBehavior spec = specs.get(stage);
            if (spec != null && !spec.requires().isEmpty()) {
                String requires = String.join(", ", spec.requires());
                return new Blocker("run.pipeline.requires",
                        "`" + pipe.name() + "` is a pipeline whose stage `" + stage
                                + "` requires injected dependencies (" + requires
                                + "), which `run` cannot supply.",
                        pipe.name(), stage, requires);
            }
        }
        return null;
    }

    /** Why the behavior the caller named cannot be driven, with the ones that can. */
    private static RunException whyNotRunnable(Ast.Module module, String name, java.util.Set<String> runnable) {
        String available = runnable.isEmpty() ? "none" : String.join(", ", runnable);
        java.util.Set<String> implemented = module.fns().stream()
                .map(Ast.FnDef::name).collect(Collectors.toSet());
        Map<String, List<String>> pipeStages = PipelineSigs.pipelineStages(module);
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (!b.name().equals(name)) {
                continue;
            }
            if (b instanceof Ast.PipeBehavior pipe) {
                Blocker blocker = pipelineBlocker(module, pipe, implemented, pipeStages);
                if (blocker == null) {
                    return fail("run.behavior.runnable",
                            "`" + name + "` is runnable. Runnable: " + available + ".", name, available);
                }
                Object[] args = new Object[blocker.args().length + 1];
                System.arraycopy(blocker.args(), 0, args, 0, blocker.args().length);
                args[args.length - 1] = available;
                return fail(blocker.key(), blocker.message() + " Runnable: " + available + ".", args);
            }
            if (b instanceof Ast.SpecBehavior spec) {
                if (!implemented.contains(name)) {
                    return fail("run.behavior.noimpl",
                            "`" + name + "` has no implementation (it is injected from Java). "
                                    + "Runnable: " + available + ".", name, available);
                }
                if (!spec.requires().isEmpty()) {
                    String requires = String.join(", ", spec.requires());
                    return fail("run.behavior.requires",
                            "`" + name + "` requires injected dependencies (" + requires
                                    + "), which `run` cannot supply. Runnable: " + available + ".",
                            name, requires, available);
                }
            }
        }
        return fail("run.behavior.unknown",
                "no behavior named `" + name + "`. Runnable: " + available + ".", name, available);
    }

    // --- input --------------------------------------------------------------------------------

    private static JsonNode[] splitInput(String name, int arity, String inputJson) {
        if (arity == 0) {
            return new JsonNode[0];
        }
        if (inputJson == null) {
            throw usage("run.input.missing", "`" + name + "` takes " + arity + " input"
                    + (arity == 1 ? "" : "s") + " — pass --input", name, arity);
        }
        JsonNode tree = parseJson(inputJson);
        if (arity == 1) {
            return new JsonNode[] {tree};
        }
        if (!tree.isArray()) {
            throw fail("run.input.notarray", "`" + name + "` takes " + arity
                    + " inputs — --input must be a JSON array of that length", name, arity);
        }
        if (tree.size() != arity) {
            throw fail("run.input.count", "`" + name + "` takes " + arity + " inputs, but --input has "
                    + tree.size(), name, arity, tree.size());
        }
        JsonNode[] args = new JsonNode[arity];
        for (int i = 0; i < arity; i++) {
            args[i] = tree.get(i);
        }
        return args;
    }

    // --- decode / encode ----------------------------------------------------------------------

    private static Object decode(MemoryClassLoader loader, String pkg, Type type, JsonNode raw, int index) {
        Decoder<JsonNode, ?> decoder = decoderFor(loader, pkg, type, index);
        Result<?> result;
        try {
            result = decoder.decode(raw, net.unit8.raoh.Path.ROOT);
        } catch (RuntimeException _) {
            // The input is not even the shape the decoder reads (an array where an object belongs),
            // which the decoder reports by throwing rather than as an issue. That is a malformed
            // --input, so it is reported as one instead of reaching the caller as a stack trace.
            throw fail("run.decode.malformed", "input #" + (index + 1) + " is not shaped like `"
                    + Type.show(type) + "` — check --input", index + 1, Type.show(type));
        }
        if (result instanceof Ok<?> ok) {
            return ok.value();
        }
        Issues issues = ((Err<?>) result).issues();
        throw new RunException("run.decode.failed",
                "input #" + (index + 1) + " could not be decoded — " + detail(issues), 1, issues,
                index + 1, detail(issues));
    }

    /** The decoder's issues as one line: each at its JSON pointer, in the order they were found. */
    private static String detail(Issues issues) {
        return issues.asList().stream()
                .map(i -> jsonPointer(i.path()) + ": " + i.message())
                .collect(Collectors.joining("; "));
    }

    /**
     * The decoder for one input type, over the JSON source. {@code --input} is JSON, so the decoders
     * have to be the ones the boundary reads JSON with: a temporal arrives as an ISO string and is
     * parsed, not handed over as a {@code java.time} value. Reading JSON with the neutral-source
     * decoders is what made a {@code Date} input impossible — anywhere, as a parameter or inside a
     * data (issue #119).
     *
     * <p>A data delegates to its generated {@code jsonDecoder()}, so a nested shape, an invariant and
     * a sum's discriminator are all read exactly as they are at the boundary. What is composed here
     * is only what has no class of its own: the primitives and the collections. A map keyed by a
     * newtype or a temporal (ADR-0040) is still left out — the generated per-data decoder remaps
     * those keys and this one does not.
     */
    private static Decoder<JsonNode, ?> decoderFor(MemoryClassLoader loader, String pkg, Type type, int index) {
        if (type instanceof Type.Prim prim) {
            return leafDecoder(prim, index);
        }
        if (type instanceof Type.Ref ref) {
            try {
                Class<?> c = loader.loadClass(ref.name().qualified());
                @SuppressWarnings("unchecked")   // the generated class's factory erases at the reflection boundary
                Decoder<JsonNode, ?> decoder = (Decoder<JsonNode, ?>) c.getMethod("jsonDecoder").invoke(null);
                return decoder;
            } catch (ReflectiveOperationException e) {
                throw fail("run.decode.nodecoder",
                        "cannot obtain a decoder for `" + ref.name().name() + "`: " + e,
                        ref.name().name(), e.toString());
            }
        }
        if (type instanceof Type.ListOf list) {
            return JsonDecoders.list(decoderFor(loader, pkg, list.element(), index));
        }
        if (type instanceof Type.SetOf set) {
            return JsonDecoders.list(decoderFor(loader, pkg, set.element(), index))
                    .map(elements -> Sets.fromList(new java.util.ArrayList<Object>(elements)));
        }
        if (type instanceof Type.MapOf map && map.key() == Type.STRING) {
            return JsonDecoders.map(decoderFor(loader, pkg, map.value(), index));
        }
        throw fail("run.decode.unsupported",
                "input #" + (index + 1) + " has type `" + Type.show(type)
                        + "`, which `run` cannot decode yet (only a data type, a primitive, or a"
                        + " collection of those).", index + 1, Type.show(type));
    }

    /** A primitive over the JSON source. {@code JsonDecoders} has no temporal factory — in JSON a
     *  temporal is a string that is then parsed — so a date reads as {@code string().date()}, the
     *  same two steps the generated JSON decoder takes. */
    private static Decoder<JsonNode, ?> leafDecoder(Type.Prim prim, int index) {
        return switch (prim) {
            case STRING -> JsonDecoders.string();
            case INT -> JsonDecoders.long_();
            case BOOL -> JsonDecoders.bool();
            case DECIMAL -> JsonDecoders.decimal();
            case DATE -> JsonDecoders.string().date();
            case DATETIME -> JsonDecoders.string().dateTime();
            case RAW -> throw fail("run.decode.raw", "input #" + (index + 1)
                    + " has the reserved Raw type, which `run` cannot decode.", index + 1);
        };
    }

    private static Object encode(String pkg, Type out, Object result) {
        if (out instanceof Type.Prim prim) {
            return encodeLeaf(prim, result);
        }
        // A collection output is encoded element by element: the runtime value is a plain
        // Collection/Map, so it carries no encoder() of its own — its elements do.
        if (out instanceof Type.ListOf list) {
            return encodeElements(pkg, list.element(), (java.util.Collection<?>) result);
        }
        if (out instanceof Type.SetOf set) {
            return encodeElements(pkg, set.element(), (java.util.Collection<?>) result);
        }
        if (out instanceof Type.MapOf map && map.key() == Type.STRING) {
            Map<String, Object> encoded = new java.util.LinkedHashMap<>();
            ((Map<?, ?>) result).forEach((k, v) -> encoded.put((String) k, encode(pkg, map.value(), v)));
            return encoded;
        }
        // A sum output is one concrete case at run time; its own class carries the right encoder.
        try {
            @SuppressWarnings("unchecked")   // the generated class's encoder() erases at the reflection boundary
            Encoder<Object, ?> encoder = (Encoder<Object, ?>) result.getClass().getMethod("encoder").invoke(null);
            return encoder.encode(result);
        } catch (ReflectiveOperationException e) {
            throw fail("run.encode.noencoder", "cannot obtain an encoder for the output `"
                    + result.getClass().getSimpleName() + "`: " + e,
                    result.getClass().getSimpleName(), e.toString());
        }
    }

    private static List<Object> encodeElements(String pkg, Type element, java.util.Collection<?> values) {
        List<Object> encoded = new java.util.ArrayList<>(values.size());
        for (Object v : values) {
            encoded.add(encode(pkg, element, v));
        }
        return encoded;
    }

    private static Object encodeLeaf(Type.Prim prim, Object value) {
        return switch (prim) {
            case STRING -> ObjectEncoders.string().encode((String) value);
            case INT -> ObjectEncoders.long_().encode((Long) value);
            case BOOL -> ObjectEncoders.bool().encode((Boolean) value);
            case DECIMAL -> ObjectEncoders.decimal().encode((java.math.BigDecimal) value);
            case DATE -> ObjectEncoders.date().encode((java.time.LocalDate) value);
            case DATETIME -> ObjectEncoders.dateTime().encode((java.time.LocalDateTime) value);
            case RAW -> throw fail("run.encode.raw",
                    "the output is the reserved Raw type, which `run` cannot encode.");
        };
    }

    // --- reflection helpers -------------------------------------------------------------------

    private static Object invoke(MemoryClassLoader loader, String pkg, String behavior, Object[] args) {
        // The public name is an interface; its no-arg constructor and erased apply live on the $Impl.
        String className = pkg + "." + behaviorClass(behavior) + "$Impl";
        try {
            Class<?> c = loader.loadClass(className);
            Object instance = c.getConstructor().newInstance();
            Class<?>[] paramTypes = new Class<?>[args.length];
            java.util.Arrays.fill(paramTypes, Object.class);
            return c.getMethod("apply", paramTypes).invoke(instance, args);
        } catch (ReflectiveOperationException e) {
            Throwable cause = e instanceof java.lang.reflect.InvocationTargetException ite
                    ? ite.getCause() : e;
            throw fail("run.behavior.failed", "`" + behavior + "` failed: " + cause,
                    behavior, String.valueOf(cause));
        }
    }

    /** The generated class capitalizes a behavior's first character (a Japanese name is unchanged),
     * matching {@code CodegenContext.behaviorClass}. */
    private static String behaviorClass(String name) {
        return Character.toUpperCase(name.charAt(0)) + name.substring(1);
    }

    // --- small utilities ----------------------------------------------------------------------

    private static String read(Path file) {
        try {
            return Files.readString(file);
        } catch (IOException e) {
            throw fail("run.read.failed", "cannot read " + file + ": " + e.getMessage(),
                    file.toString(), e.getMessage());
        }
    }

    /** The module name for a header-less source: the file name without its extension, or {@code main}
     * when that is not a usable identifier. */
    static String moduleName(Path file) {
        String fileName = file.getFileName().toString();
        int dot = fileName.indexOf('.');
        String stem = dot < 0 ? fileName : fileName.substring(0, dot);
        if (stem.isEmpty() || !Character.isLetter(stem.charAt(0))) {
            return "main";
        }
        for (int i = 1; i < stem.length(); i++) {
            char ch = stem.charAt(i);
            if (!Character.isLetterOrDigit(ch) && ch != '_') {
                return "main";
            }
        }
        return stem;
    }

    private static String jsonPointer(net.unit8.raoh.Path path) {
        String p = path.toJsonPointer();
        return p.isEmpty() ? "(root)" : p;
    }

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static JsonNode parseJson(String input) {
        try {
            return JSON.readTree(input);
        } catch (Exception e) {
            throw fail("run.input.badjson", "--input is not valid JSON: " + e.getMessage(),
                    e.getMessage());
        }
    }

    private static String writeJson(Object tree) {
        try {
            return JSON.writeValueAsString(tree);
        } catch (Exception e) {
            throw fail("run.output.json", "could not render the output as JSON: " + e.getMessage(),
                    e.getMessage());
        }
    }
}
