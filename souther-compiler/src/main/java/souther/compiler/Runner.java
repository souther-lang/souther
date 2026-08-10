package souther.compiler;

import souther.compiler.ast.Ast;
import souther.compiler.check.PipelineSigs;
import souther.compiler.check.Sig;
import souther.compiler.check.TypeOps;
import souther.compiler.check.BoundaryMapKey;
import souther.compiler.types.MapKeyRepresentation;
import souther.compiler.types.LeafScalar;
import souther.compiler.check.BoundaryInput;
import souther.compiler.check.BoundaryOutput;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.codegen.Backend;
import souther.compiler.diag.Located;
import souther.compiler.diag.Messages;
import net.unit8.raoh.Err;
import net.unit8.raoh.Issues;
import net.unit8.raoh.ResourceBundleMessageResolver;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Result;
import net.unit8.raoh.decode.Decoder;
import net.unit8.raoh.decode.ObjectDecoders;
import net.unit8.raoh.decode.builtin.StringDecoder;
import net.unit8.raoh.json.JsonDecoders;
import net.unit8.raoh.encode.Encoder;
import net.unit8.raoh.encode.ObjectEncoders;

import souther.runtime.Representations;
import souther.runtime.Sets;

import tools.jackson.core.JsonGenerator;
import tools.jackson.core.JsonParser;
import tools.jackson.core.StreamReadConstraints;
import tools.jackson.core.StreamWriteConstraints;
import tools.jackson.core.TokenStreamContext;
import tools.jackson.core.exc.StreamConstraintsException;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.IOException;
import java.io.StringWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Drives a compiled behavior from the command line: {@code souther run <file.sou> [-cp <path>]
 * [--behavior <name>] [--input <json>]}. The runner is itself the Java boundary (spec section 13) —
 * it decodes the JSON input into the behavior's parameter types through their derived decoders,
 * applies the behavior, and encodes the returned domain value back to JSON through its derived
 * encoder. Souther keeps no I/O of its own; a header-less {@code .sou} is named after the file (see
 * {@link Parser}).
 *
 * <p>The runner drives one {@code .sou} file. Stdlib imports resolve, and an import of another user
 * module resolves against {@code -cp} — the same class path {@code compile} takes, read for the
 * imported module's declarations and holding the classes the behavior then runs against. A behavior
 * is runnable when it has a {@code let} and no
 * {@code depends on}, or when it is a {@code >->} pipeline whose stages are all themselves runnable
 * (each has a {@code let} and no {@code depends on}) — such a pipeline compiles to a no-arg {@code
 * $Impl} that chains the stages, so it runs like any other behavior. An injected behavior (no
 * implementation), one that needs injected dependencies, or a pipeline with such a stage has nothing
 * for {@code run} to supply; each is refused with a reason.
 *
 * <p>Being runnable is not the whole of it. The runner is another module's reader, reaching the
 * compiled behavior by reflection from {@code souther.compiler}, and what a module publishes is what
 * codegen marks public. So {@code run} drives a behavior the module exposes, and a runnable one kept
 * to the module is refused as that — before its input type is asked for a decoder, which is the same
 * refusal wearing another name.
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
                // issues; rewriting it here is what puts the decoder's own wording into the reader's
                // language
                resolved = args.clone();
                resolved[resolved.length - 1] = detail(issues.resolve(DECODE_MESSAGES, locale));
            }
            String text = Messages.get(messageKey, locale, resolved);
            return exitCode == 2 ? text + "\n" + Messages.get("run.usage.line", locale) : text;
        }
    }

    /**
     * The decoder's own message catalog, which its issues are written against. It answers per issue
     * rather than per code: an issue names the constraint that rejected the value, so a code covering
     * several of them — {@code out_of_range} states a lower bound, an upper bound, or both — is
     * described as the one it is. An entry whose placeholders the issue cannot fill is skipped rather
     * than half-filled, and where no entry applies the message the decoder already wrote stands.
     */
    private static final ResourceBundleMessageResolver DECODE_MESSAGES =
            new ResourceBundleMessageResolver("net.unit8.raoh.messages");

    /** A failure that names a catalog key: the English literal for a Java caller, the key for the
     * command line's chosen locale. */
    private static RunException fail(String key, String message, Object... args) {
        return new RunException(key, message, 1, null, args);
    }

    /** Parses the {@code run} subcommand's arguments (everything after {@code run}) and runs it,
     *  collecting the compile's warnings into {@code warningsOut} for the caller to render —
     *  running a module says what compiling it would have said. */
    static String runCli(String[] args, List<Located> warningsOut) {
        Path file = null;
        String behaviorName = null;
        String inputJson = null;
        List<Path> classPath = new ArrayList<>();
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "--behavior" -> behaviorName = value(args, ++i, "--behavior");
                case "--input" -> inputJson = value(args, ++i, "--input");
                case "-cp", "--class-path" -> {
                    String option = args[i];
                    classPath.addAll(entriesOf(value(args, ++i, option)));
                }
                default -> {
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
        return run(file, behaviorName, inputJson, warningsOut, pathOf(classPath));
    }

    /** A class path as its entries, in the order they are searched. */
    static List<Path> entriesOf(String written) {
        List<Path> entries = new ArrayList<>();
        for (String entry : written.split(java.io.File.pathSeparator)) {
            if (!entry.isBlank()) {
                entries.add(Path.of(entry));
            }
        }
        return entries;
    }

    private static ModulePath pathOf(List<Path> entries) {
        return entries.isEmpty() ? ModulePath.EMPTY : ModulePath.ofClassPath(entries);
    }

    private static String value(String[] args, int i, String option) {
        if (i >= args.length) {
            throw usage("run.usage.optionvalue", "`" + option + "` needs a value", option);
        }
        return args[i];
    }

    private static RunException usage(String key, String problem, Object... args) {
        return new RunException(key, problem
                + "\nusage: souther run <file.sou> [-cp <path>] [--behavior <name>] [--input <json>]",
                2, null, args);
    }

    /** Compiles {@code file}, drives {@code behaviorName} with {@code inputJson}, and returns the
     * encoded output as JSON text. {@code behaviorName} may be null when the module holds exactly
     * one runnable behavior; {@code inputJson} may be null for a zero-argument behavior. */
    public static String run(Path file, String behaviorName, String inputJson) {
        return run(file, behaviorName, inputJson, new ArrayList<>(), ModulePath.EMPTY);
    }

    /**
     * As {@link #run(Path, String, String)}, resolving an import naming no module in {@code file}
     * against {@code path} and running against its classes, and collecting the compile's warnings
     * into {@code warningsOut}.
     */
    static String run(Path file, String behaviorName, String inputJson, List<Located> warningsOut,
                      ModulePath path) {
        String source = read(file);
        String moduleName = moduleName(file);

        // One compilation answers all of it. Re-reading the source here to find the behavior and
        // its signature would resolve every name a second time, against a tree this compile has
        // already produced.
        Compilation compilation = Compiler.compiled(source, moduleName, warningsOut, path);
        // The module this file declares, and not one it reached: what the path holds is read for its
        // declarations and is no part of what this compilation declares.
        Ast.Module module = compilation.module(compilation.modules().get(0));
        Map<String, Sig> sigs = compilation.signatures(module.name());

        Ast.BehaviorDef spec = resolveBehavior(module, behaviorName);
        Sig sig = sigs.get(spec.name());

        // The compilation's own — its classes over the ones the path already built. Composing a
        // loader here instead would be a second statement of that order, which is the one thing
        // about loading this compiler settles in a single place.
        ClassLoader loader = compilation.loader();
        Object[] args = decodeInputs(loader, spec.name(), sig.ins(), inputJson);

        Object result = invoke(loader, module.name(), spec.name(), args);
        Object encoded = encodeOutput(loader, module.name(), spec.name(), sig.out(), result);
        return writeJson(encoded);
    }

    // --- behavior selection ---------------------------------------------------------------------

    /** The names a behavior depends on, as a message lists them. */
    private static String dependencyNames(Ast.SpecBehavior spec) {
        List<String> names = new java.util.ArrayList<>();
        for (Ast.Var dep : spec.dependsOn()) {
            names.add(dep.bare());
        }
        return String.join(", ", names);
    }

    /**
     * Whether the module publishes {@code name}. This is the same question codegen asks before it
     * marks a generated class {@code ACC_PUBLIC} ({@code CodegenContext.pub}), and it is asked here
     * for that reason: the runner reaches the compiled behavior by reflection from another package,
     * which the JVM allows only for a class the module published. A module with no {@code exposing}
     * list keeps nothing to itself, so a header-less file publishes everything in it.
     */
    private static boolean exposes(Ast.Module module, String name) {
        return module.exposing().isEmpty() || module.exposing().contains(name);
    }

    /**
     * The behavior to drive.
     *
     * <p>Two questions are asked, and they are not the same one. Whether a behavior can run at all is
     * asked of the module's own workings — it has a {@code let} and needs nothing injected. Whether
     * {@code run} can reach it is asked at the module's edge, because {@code run} stands outside the
     * module and arrives the way any other reader does. A behavior can answer the first and not the
     * second, and one the module keeps to itself is exactly that.
     */
    private static Ast.BehaviorDef resolveBehavior(Ast.Module module, String requestedSpelling) {
        // What `--behavior` was given is a name arriving from outside, and it is looked up
        // against names the source settled.
        String requested = Reserved.name(requestedSpelling);
        java.util.Set<String> implemented = module.fns().stream()
                .map(Ast.FnDef::name).collect(Collectors.toSet());
        Map<String, List<Ast.Var>> pipeStages = PipelineSigs.pipelineStages(module);
        Map<String, Ast.BehaviorDef> drivable = new java.util.LinkedHashMap<>();
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (!exposes(module, b.name())) {
                continue;
            }
            if (b instanceof Ast.SpecBehavior spec
                    && implemented.contains(spec.name()) && spec.dependsOn().isEmpty()) {
                drivable.put(spec.name(), spec);
            } else if (b instanceof Ast.PipeBehavior pipe
                    && pipelineBlocker(module, pipe, implemented, pipeStages) == null) {
                drivable.put(pipe.name(), pipe);
            }
        }
        if (requested == null) {
            if (drivable.size() == 1) {
                return drivable.values().iterator().next();
            }
            if (drivable.isEmpty()) {
                throw fail("run.behavior.none", "no behavior in this module can be run. "
                        + "`run` runs a behavior that is runnable — implemented in Souther and"
                        + " needing nothing injected, a `>->` pipeline when every stage is — and"
                        + " that the module exposes.");
            }
            String names = String.join(", ", drivable.keySet());
            throw usage("run.behavior.several",
                    "several behaviors can be run — pick one with --behavior: " + names, names);
        }
        Ast.BehaviorDef found = drivable.get(requested);
        if (found != null) {
            return found;
        }
        throw whyNotRunnable(module, requested, drivable.keySet());
    }

    /** A reason a behavior cannot be driven, in both forms: the catalog key with its arguments, and
     * the English literal. The list of behaviors that can be driven is appended to both. */
    private record Blocker(String key, String message, Object... args) {}

    /**
     * Why a {@code >->} pipeline cannot be driven by {@code run}, or null when every stage is
     * in-language. A pipeline whose flattened stages all have a {@code let} and no {@code depends on}
     * compiles to an {@code $Impl} with a public no-arg constructor, so it runs exactly like a simple
     * behavior. A stage with no implementation (injected from Java) or one that needs its own injected
     * dependencies would make that constructor take those behaviors, which {@code run} cannot supply.
     */
    private static Blocker pipelineBlocker(Ast.Module module, Ast.PipeBehavior pipe,
            java.util.Set<String> implemented, Map<String, List<Ast.Var>> pipeStages) {
        Map<String, Ast.SpecBehavior> specs = new java.util.HashMap<>();
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (b instanceof Ast.SpecBehavior spec) {
                specs.put(spec.name(), spec);
            }
        }
        for (Ast.Var named : PipelineSigs.flattenStages(pipe.stages(), pipeStages, pipe.pos())) {
            String stage = named.bare();
            if (!implemented.contains(stage)) {
                return new Blocker("run.pipeline.noimpl",
                        "`" + pipe.name() + "` is a pipeline whose stage `" + stage
                                + "` has no implementation (it is injected from Java), which `run` cannot supply.",
                        pipe.name(), stage);
            }
            Ast.SpecBehavior spec = specs.get(stage);
            if (spec != null && !spec.dependsOn().isEmpty()) {
                String dependencies = dependencyNames(spec);
                return new Blocker("run.pipeline.depends",
                        "`" + pipe.name() + "` is a pipeline whose stage `" + stage
                                + "` depends on injected dependencies (" + dependencies
                                + "), which `run` cannot supply.",
                        pipe.name(), stage, dependencies);
            }
        }
        return null;
    }

    /**
     * Why the behavior the caller named cannot be driven, with the ones that can.
     *
     * <p>A behavior the module keeps to itself is answered as that and nothing else, ahead of the
     * reasons that read its workings. Those reasons describe what is inside the module, which is not
     * what a reader standing outside it is owed, and following one of them would only bring the
     * author back to the same refusal.
     */
    private static RunException whyNotRunnable(Ast.Module module, String name, java.util.Set<String> drivable) {
        String available = drivable.isEmpty() ? "none" : String.join(", ", drivable);
        java.util.Set<String> implemented = module.fns().stream()
                .map(Ast.FnDef::name).collect(Collectors.toSet());
        Map<String, List<Ast.Var>> pipeStages = PipelineSigs.pipelineStages(module);
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (!b.name().equals(name)) {
                continue;
            }
            if (!exposes(module, name)) {
                return fail("run.behavior.notexposed",
                        "`" + name + "` is not exposed, and `run` drives a behavior the module"
                                + " exposes — add it to `exposing`. Available to run: " + available + ".",
                        name, available);
            }
            if (b instanceof Ast.PipeBehavior pipe) {
                Blocker blocker = pipelineBlocker(module, pipe, implemented, pipeStages);
                if (blocker == null) {
                    return fail("run.behavior.runnable",
                            "`" + name + "` is runnable. Available to run: " + available + ".", name, available);
                }
                Object[] args = new Object[blocker.args().length + 1];
                System.arraycopy(blocker.args(), 0, args, 0, blocker.args().length);
                args[args.length - 1] = available;
                return fail(blocker.key(), blocker.message() + " Available to run: " + available + ".", args);
            }
            if (b instanceof Ast.SpecBehavior spec) {
                if (!implemented.contains(name)) {
                    return fail("run.behavior.noimpl",
                            "`" + name + "` has no implementation (it is injected from Java). "
                                    + "Available to run: " + available + ".", name, available);
                }
                if (!spec.dependsOn().isEmpty()) {
                    String dependencies = dependencyNames(spec);
                    return fail("run.behavior.depends",
                            "`" + name + "` depends on injected dependencies (" + dependencies
                                    + "), which `run` cannot supply. Available to run: " + available + ".",
                            name, dependencies, available);
                }
            }
        }
        return fail("run.behavior.unknown",
                "no behavior named `" + name + "`. Available to run: " + available + ".", name, available);
    }

    // --- input --------------------------------------------------------------------------------

    /**
     * The behavior's arguments, read from {@code --input}.
     *
     * <p>How the text is cut into arguments is not a question the syntax answers. From two inputs up
     * it is: the text is a JSON array of that length, positionally, and an array of another length or
     * no array at all is refused by arity alone. A single input is written as it stands, and there the
     * same text has two readings — for {@code (xs: List<Int>)}, {@code [1,2,3]} is the argument, and
     * {@code [[1,2,3]]} is the argument written inside the argument array the two-input form takes.
     * Arity cannot tell them apart; only decoding against the parameter type can. So the split and the
     * decode are one step, taken with the types in hand.
     */
    private static Object[] decodeInputs(ClassLoader loader, String name,
                                         List<BoundaryInput> ins, String inputJson) {
        int arity = ins.size();
        if (arity == 0) {
            return new Object[0];
        }
        if (inputJson == null) {
            throw usage("run.input.missing", "`" + name + "` takes " + arity + " input"
                    + (arity == 1 ? "" : "s") + " — pass --input", name, arity);
        }
        JsonNode tree = parseJson(inputJson);
        if (arity == 1) {
            return new Object[] {decodeSoleInput(loader, ins.get(0), tree)};
        }
        if (!tree.isArray()) {
            throw fail("run.input.notarray", "`" + name + "` takes " + arity
                    + " inputs — --input must be a JSON array of that length", name, arity);
        }
        if (tree.size() != arity) {
            throw fail("run.input.count", "`" + name + "` takes " + arity + " inputs, but --input has "
                    + tree.size(), name, arity, tree.size());
        }
        Object[] args = new Object[arity];
        for (int i = 0; i < arity; i++) {
            args[i] = decode(loader, ins.get(i), tree.get(i), i);
        }
        return args;
    }

    /**
     * The sole input, read as it stands — and only when that fails, read again as the value a
     * one-element array wraps.
     *
     * <p>The order is what makes the second reading safe: an input that is an array in its own right
     * decodes on the first attempt and never reaches it. Being an array is not the mistake; failing as
     * the value while succeeding as the array's sole element is. When the element fails too, the input
     * is wrong for some other reason and the decoder's own report is what says so.
     */
    private static Object decodeSoleInput(ClassLoader loader, BoundaryInput shape,
                                          JsonNode tree) {
        try {
            return decode(loader, shape, tree, 0);
        } catch (RunException asWritten) {
            if (tree.isArray() && tree.size() == 1 && decodes(loader, shape, tree.get(0))) {
                throw fail("run.input.wrapped", "This behavior has one parameter. Pass its value"
                        + " directly to --input; remove the outer array.");
            }
            throw asWritten;
        }
    }

    /** Whether {@code raw} decodes as {@code type}, asked without reporting anything. */
    private static boolean decodes(ClassLoader loader, BoundaryInput shape, JsonNode raw) {
        try {
            decode(loader, shape, raw, 0);
            return true;
        } catch (RunException _) {
            return false;
        }
    }

    // --- decode / encode ----------------------------------------------------------------------

    private static Object decode(ClassLoader loader, BoundaryInput shape, JsonNode raw,
                                 int index) {
        Decoder<JsonNode, ?> decoder = decoderFor(loader, shape, index);
        Result<?> result;
        try {
            result = decoder.decode(raw, net.unit8.raoh.Path.ROOT);
        } catch (RuntimeException _) {
            // The input is not even the shape the decoder reads (an array where an object belongs),
            // which the decoder reports by throwing rather than as an issue. That is a malformed
            // --input, so it is reported as one instead of reaching the caller as a stack trace.
            throw fail("run.decode.malformed", "input #" + (index + 1) + " is not shaped like `"
                    + Type.show(shape.type()) + "` — check --input", index + 1,
                    Type.show(shape.type()));
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
     * is only what has no class of its own: the primitives and the collections.
     */
    private static Decoder<JsonNode, ?> decoderFor(ClassLoader loader, BoundaryInput shape,
                                                   int index) {
        return switch (shape) {
            case BoundaryInput.Scalar s -> leafDecoder(s.scalar());
            case BoundaryInput.Nominal n -> codecOf(loader, n.name(), "jsonDecoder");
            case BoundaryInput.ListOf l -> JsonDecoders.list(decoderFor(loader, l.element(), index));
            case BoundaryInput.SetOf s -> JsonDecoders.list(decoderFor(loader, s.element(), index))
                    .map(elements -> Sets.fromList(new java.util.ArrayList<Object>(elements)));
            case BoundaryInput.MapOf m -> {
                Decoder<Object, ?> key = keyDecoder(loader, m.key());
                yield JsonDecoders.map(decoderFor(loader, m.value(), index))
                        .flatMapWithPath((entries, path) -> rekey(key, entries, path));
            }
        };
    }

    /**
     * The decoder for a boundary map's key. A key reaches this already read out of the JSON object
     * that carried it, so what it decodes from is a string rather than a {@code JsonNode} — the
     * neutral source, whichever source the map itself came from. This is the decoder
     * {@code CodecGen.emitKeyDecoder} builds, in Java.
     *
     * <p>Which key types arrive here is not decided again, and is not asked again either: the witness
     * the map-key rule answers with travels in the shape. A named key runs its own decoder, and a
     * representation is the string leaf, parsed for a temporal.
     */
    private static Decoder<Object, ?> keyDecoder(ClassLoader loader, BoundaryMapKey key) {
        return switch (key.representation()) {
            case MapKeyRepresentation.StringNewtype n -> codecOf(loader, n.name(), "decoder");
            case MapKeyRepresentation.UnitEnum e -> codecOf(loader, e.name(), "decoder");
            case MapKeyRepresentation.Text _ -> text();
            case MapKeyRepresentation.Date _ -> text().date();
            case MapKeyRepresentation.DateTime _ -> text().dateTime();
        };
    }

    /** The string leaf a key is read through. Text arriving from outside is canonical, which is what
     *  the leaf makes it (ADR-0096). */
    private static StringDecoder<Object> text() {
        return ObjectDecoders.string().normalize();
    }

    /**
     * A decoded {@code Map<String, V>} rekeyed by the key type's own decoder, which is where a key's
     * invariant is enforced and a temporal key is parsed.
     *
     * <p>A bad key is reported at that key's own path, and every key is read before the result is
     * settled, so a map with two bad keys says so about both. A {@code String} key is rekeyed like
     * any other: the keys of a decoded object do not pass the string leaf, so leaving them alone is
     * the one place a boundary would hand over text it had not made canonical.
     *
     * <p>Two keys that decode to one key are refused rather than collapsed. Making a key canonical
     * is what lets an object arrive with the same key written twice, and a map holding one entry
     * where the input wrote two is a value the input never described — so the second is a failure at
     * its own key, not the winner of an overwrite.
     */
    private static Result<Map<Object, Object>> rekey(Decoder<Object, ?> key, Map<String, ?> entries,
                                                     net.unit8.raoh.Path path) {
        Map<Object, Object> out = new java.util.LinkedHashMap<>();
        Issues issues = Issues.EMPTY;
        for (Map.Entry<String, ?> entry : entries.entrySet()) {
            net.unit8.raoh.Path at = path.append(entry.getKey());
            Result<?> decoded = key.decode(entry.getKey(), at);
            if (decoded instanceof Err<?> err) {
                issues = issues.merge(err.issues());
                continue;
            }
            Object rekeyed = ((Ok<?>) decoded).value();
            if (out.containsKey(rekeyed)) {
                issues = issues.merge(((Err<?>) Result.fail(at, DUPLICATE_KEY, DUPLICATE_KEY_MESSAGE))
                        .issues());
            } else {
                out.put(rekeyed, entry.getValue());
            }
        }
        return issues.isEmpty() ? new Ok<>(out) : new Err<>(issues);
    }

    /** What a key colliding with one already read is reported as — the code and the wording the
     *  generated rekey helper uses, so the two paths refuse the same input the same way. */
    private static final String DUPLICATE_KEY = "duplicate_key";
    private static final String DUPLICATE_KEY_MESSAGE = "two keys are the same key once decoded";

    /**
     * The named static decoder factory of a generated class — {@code jsonDecoder} for a value read
     * from JSON, {@code decoder} for a map key, which is read from the string the object carried.
     * Either erases at the reflection boundary.
     *
     * <p>The name came out of the witness, so it is one a model declared and one this compilation
     * generated a class for, and that class carries both factories. There is nothing here to report:
     * a reflective failure would mean the class this run emitted is not the class it emitted, which
     * is not something a reader of the boundary can say anything useful about.
     */
    private static <I> Decoder<I, ?> codecOf(ClassLoader loader, TypeName type, String factory) {
        try {
            @SuppressWarnings("unchecked")
            Decoder<I, ?> decoder = (Decoder<I, ?>)
                    loader.loadClass(type.qualified()).getMethod(factory).invoke(null);
            return decoder;
        } catch (ReflectiveOperationException e) {
            throw new IllegalStateException("`" + type.qualified() + "` has no `" + factory + "()`", e);
        }
    }

    /** A scalar over the JSON source. {@code JsonDecoders} has no temporal factory — in JSON a
     *  temporal is a string that is then parsed — so a date reads as {@code string().date()}, the
     *  same two steps the generated JSON decoder takes. */
    private static Decoder<JsonNode, ?> leafDecoder(LeafScalar scalar) {
        return switch (scalar) {
            case STRING -> JsonDecoders.string();
            case INT -> JsonDecoders.long_();
            case BOOL -> JsonDecoders.bool();
            case DECIMAL -> JsonDecoders.decimal();
            case DATE -> JsonDecoders.string().date();
            case DATETIME -> JsonDecoders.string().dateTime();
        };
    }

    /**
     * The whole output, encoded.
     *
     * <p>Encoding descends the value by recursion, so a value that nests deeply enough runs the stack
     * out before the writer ever counts a level. A behavior can build a value deeper than anything it
     * was handed, so this is reached from input the boundary accepted. A {@code StackOverflowError}
     * is not a {@code RunException}, so left alone it reaches the caller as a stack trace.
     */
    private static Object encodeOutput(ClassLoader loader, String pkg, String behavior,
                                       BoundaryOutput out, Object result) {
        try {
            return encode(loader, pkg, behavior, out, result);
        } catch (StackOverflowError _) {
            throw fail("run.encode.toodeep",
                    "the output nests too deeply for this boundary to encode.");
        }
    }

    /**
     * The output as its declared type writes it. Which encoder that is follows the type the behavior
     * declared, never the class the answer happens to have arrived in: a case of a sum carries no
     * discriminator on its own encoder — only the sum's writes one — so taking the encoder off the
     * runtime value would answer a form the same sum's decoder then refuses.
     */
    private static Object encode(ClassLoader loader, String pkg, String behavior,
                                 BoundaryOutput out, Object result) {
        return switch (out) {
            case BoundaryOutput.Scalar s -> encodeLeaf(s.scalar(), result);
            // A collection output is encoded element by element: the runtime value is a plain
            // Collection/Map, so it carries no encoder() of its own — its elements do.
            case BoundaryOutput.ListOf l ->
                    encodeElements(loader, pkg, behavior, l.element(), (java.util.Collection<?>) result);
            // A Set and a Map are put in the order their encoded members give ([#collections]), which
            // is done here as well as in the generated codecs because this is where the shape is still
            // known: encoded, a Set and a List are both a java.util.List, and only one is reordered.
            case BoundaryOutput.SetOf s -> Representations.sortedArray(
                    encodeElements(loader, pkg, behavior, s.element(), (java.util.Collection<?>) result));
            case BoundaryOutput.MapOf m -> {
                Map<String, Object> encoded = new java.util.LinkedHashMap<>();
                ((Map<?, ?>) result).forEach((k, v) -> encoded.put(encodeKey(loader, m.key(), k),
                        encode(loader, pkg, behavior, m.value(), v)));
                yield Representations.sortedObject(encoded);
            }
            case BoundaryOutput.Nominal n ->
                    encodeThrough(loader, n.name().qualified(), result);
            // A union nobody named is generated as the behavior's result type, which is where its
            // encoder is (spec 19.8). It is the only output with no name in the source, so it is the
            // behavior that says which class to reach for.
            case BoundaryOutput.Cases c -> encodeThrough(loader,
                    pkg + "." + Backend.behaviorResultClass(behavior), result);
        };
    }

    /**
     * A map's key, written as the text it crosses as. Each kind already has the encoder that writes
     * it — the string leaf, the ISO form of a temporal, the newtype's bare value, the enumeration's
     * case name — and which kind it is travelled here rather than being asked again.
     */
    private static String encodeKey(ClassLoader loader, BoundaryMapKey key, Object value) {
        return (String) switch (key.representation()) {
            case MapKeyRepresentation.Text _ -> encodeLeaf(LeafScalar.STRING, value);
            case MapKeyRepresentation.Date _ -> encodeLeaf(LeafScalar.DATE, value);
            case MapKeyRepresentation.DateTime _ -> encodeLeaf(LeafScalar.DATETIME, value);
            case MapKeyRepresentation.StringNewtype n ->
                    encodeThrough(loader, n.name().qualified(), value);
            case MapKeyRepresentation.UnitEnum e ->
                    encodeThrough(loader, e.name().qualified(), value);
        };
    }

    /** {@code result} through the derived {@code encoder()} of the named generated class. Every type
     *  a witness names has one, and so does the class a behavior's anonymous answer is generated as,
     *  so this reads what was emitted rather than asking whether it was. */
    private static Object encodeThrough(ClassLoader loader, String className,
                                        Object result) {
        try {
            @SuppressWarnings("unchecked")   // the generated class's encoder() erases at the reflection boundary
            Encoder<Object, ?> encoder = (Encoder<Object, ?>)
                    loader.loadClass(className).getMethod("encoder").invoke(null);
            return encoder.encode(result);
        } catch (ReflectiveOperationException e) {
            throw new IllegalStateException("`" + className + "` has no `encoder()`", e);
        }
    }

    private static List<Object> encodeElements(ClassLoader loader, String pkg, String behavior,
                                               BoundaryOutput element, java.util.Collection<?> values) {
        List<Object> encoded = new java.util.ArrayList<>(values.size());
        for (Object v : values) {
            encoded.add(encode(loader, pkg, behavior, element, v));
        }
        return encoded;
    }

    private static Object encodeLeaf(LeafScalar scalar, Object value) {
        return switch (scalar) {
            case STRING -> ObjectEncoders.string().encode((String) value);
            case INT -> ObjectEncoders.long_().encode((Long) value);
            case BOOL -> ObjectEncoders.bool().encode((Boolean) value);
            case DECIMAL -> ObjectEncoders.decimal()
                    .encode(Representations.canonicalNumber((java.math.BigDecimal) value));
            case DATE -> ObjectEncoders.date().encode((java.time.LocalDate) value);
            case DATETIME -> ObjectEncoders.dateTime().encode((java.time.LocalDateTime) value);
        };
    }

    // --- reflection helpers -------------------------------------------------------------------

    /**
     * The behavior applied to its arguments.
     *
     * <p>The two ways this can fail are two different things and are told apart. The behavior itself
     * throwing arrives as an {@code InvocationTargetException} and is the behavior's failure. Anything
     * else — the class not there, no no-arg constructor, no reachable {@code apply} — is the runner
     * unable to start it, which after the exposed check is codegen and the runner disagreeing rather
     * than anything the module did. Reported as one, the second reads as the behavior having run and
     * failed, and sends the author looking through a body that was never entered.
     */
    private static Object invoke(ClassLoader loader, String pkg, String behavior, Object[] args) {
        // The public name is an interface; its no-arg constructor and erased apply live on the $Impl.
        String className = pkg + "." + behaviorClass(behavior) + "$Impl";
        try {
            Class<?> c = loader.loadClass(className);
            Object instance = c.getConstructor().newInstance();
            Class<?>[] paramTypes = new Class<?>[args.length];
            java.util.Arrays.fill(paramTypes, Object.class);
            return c.getMethod("apply", paramTypes).invoke(instance, args);
        } catch (java.lang.reflect.InvocationTargetException e) {
            Throwable cause = e.getCause();
            throw fail("run.behavior.failed", "`" + behavior + "` failed: " + cause,
                    behavior, String.valueOf(cause));
        } catch (ReflectiveOperationException e) {
            throw fail("run.behavior.unreachable",
                    "`" + behavior + "` could not be started — the compiled `" + className
                            + "` is not reachable: " + e + ". This is a defect in the compiler,"
                            + " not in the module.", behavior, className, e.toString());
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
        // Canonicalized before it is judged, not after: a file delivered by macOS carries its name
        // decomposed, and a combining mark is not a letter or a digit, so the same file would be
        // `main` on one machine and its own name on another.
        String stem = Reserved.name(dot < 0 ? fileName : fileName.substring(0, dot));
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

    /** How deep the mapper reads and writes before it refuses, counted in levels of JSON. */
    private static final int READ_DEPTH_LIMIT =
            StreamReadConstraints.defaults().getMaxNestingDepth();
    private static final int WRITE_DEPTH_LIMIT =
            StreamWriteConstraints.defaults().getMaxNestingDepth();

    /**
     * The depth a context stands at when its side has just refused a value for nesting. The two
     * sides count differently, measured: reading stands on the level it refused to enter, and
     * writing on the last level it accepted.
     */
    private static final int READ_REFUSAL_DEPTH = READ_DEPTH_LIMIT + 1;
    private static final int WRITE_REFUSAL_DEPTH = WRITE_DEPTH_LIMIT;

    /**
     * Parses {@code --input}.
     *
     * <p>The parser is made here rather than left to {@code readTree(String)} because the exception a
     * depth refusal throws carries neither a location nor the parser that raised it. Holding the
     * parser is what lets the refusal name the path it gave up at, the way every other thing the
     * boundary rejects is named.
     *
     * <p>Input with nothing in it reads as the missing node rather than as no node at all, so an
     * empty {@code --input} reaches the same refusal as input of the wrong shape.
     */
    private static JsonNode parseJson(String input) {
        JsonParser parser = JSON.createParser(input);
        try {
            JsonNode tree = JSON.readTree(parser);
            return tree == null ? JSON.missingNode() : tree;
        } catch (Exception e) {
            TokenStreamContext where = parser.streamReadContext();
            if (refusedForDepth(e, where, READ_REFUSAL_DEPTH)) {
                throw tooDeep("run.input.toodeep", "--input nests deeper than this boundary accepts",
                        where, READ_DEPTH_LIMIT);
            }
            throw fail("run.input.badjson", "--input is not valid JSON: " + e.getMessage(),
                    e.getMessage());
        } finally {
            parser.close();
        }
    }

    /** Renders the encoded output. The generator is held for the same reason the parser is. */
    private static String writeJson(Object tree) {
        StringWriter out = new StringWriter();
        JsonGenerator generator = JSON.createGenerator(out);
        try {
            JSON.writeValue(generator, tree);
            return out.toString();
        } catch (Exception e) {
            // read before the close in `finally`, which resets the generator's context to the root
            TokenStreamContext where = generator.streamWriteContext();
            if (refusedForDepth(e, where, WRITE_REFUSAL_DEPTH)) {
                throw tooDeep("run.output.toodeep",
                        "the output nests deeper than this boundary can render",
                        where, WRITE_DEPTH_LIMIT);
            }
            throw fail("run.output.json", "could not render the output as JSON: " + e.getMessage(),
                    e.getMessage());
        } finally {
            generator.close();
        }
    }

    /**
     * Whether {@code failure} is the reader or writer refusing a value for its depth.
     *
     * <p>{@code StreamConstraintsException} is not the depth refusal alone: the reader raises the
     * same type for a number too long, a name too long, a string too long, a document too long and a
     * token count too high. Which limit it was is asked of the context's own depth rather than of
     * the exception's text, which is prose Jackson is free to rewrite.
     *
     * <p>Standing at {@code refusalDepth} is the depth refusal and can be nothing else. A value
     * refused for another reason stands shallower: the reader admits scalars at every level up to
     * the limit, so the deepest a long number can be refused at is one level short of where a
     * refusal for depth stands. Every other constraint keeps the wording it had.
     */
    private static boolean refusedForDepth(Exception failure, TokenStreamContext where,
                                           int refusalDepth) {
        return failure instanceof StreamConstraintsException
                && where.getNestingDepth() >= refusalDepth;
    }

    /**
     * A value that nests deeper than the boundary handles, reported where it stopped.
     *
     * <p>The limit is named rather than the value's own depth: reading and writing both stop at the
     * level that crosses the limit, so how much deeper the value goes was never counted. What is
     * counted is levels of JSON, which is not levels of the data — one level of a self-referential
     * data spends a level for its object and another for the list that carries the next one.
     */
    private static RunException tooDeep(String key, String english, TokenStreamContext where,
                                        int limit) {
        String path = depthPath(where);
        return fail(key, english + ": " + path + " and below (JSON nesting past " + limit
                + " levels)", path, limit);
    }

    /** How much of the path to the deepest level is worth reading. */
    private static final int DEPTH_PATH_SEGMENTS = 8;

    /**
     * The path the depth limit was reached at, cut short. Nesting that deep is nesting that repeats,
     * so the whole pointer runs to hundreds of segments of the same few names; the head is the part
     * that says which branch went deep.
     */
    private static String depthPath(TokenStreamContext where) {
        String pointer = where.pathAsPointer().toString();
        if (pointer.isEmpty()) {
            return "(root)";
        }
        int cut = 0;
        for (int i = 0; i < DEPTH_PATH_SEGMENTS; i++) {
            int next = pointer.indexOf('/', cut + 1);
            if (next < 0) {
                return pointer;
            }
            cut = next;
        }
        return pointer.substring(0, cut) + "/…";
    }
}
