package souther.compiler.meta;

import souther.compiler.stdlib.LibraryNames;
import souther.compiler.ast.Ast;
import souther.compiler.check.DeclaredNames;
import souther.compiler.check.Exposing;
import souther.compiler.check.Preserved;
import souther.compiler.check.Scoping;
import souther.compiler.check.Registry;
import souther.compiler.codegen.Backend;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Region;
import souther.compiler.cst.SourceLayout;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.check.BehaviorImplementation;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Reading a module back from what {@link ModuleMetadata} wrote into its classes: the declarations
 * another project needs in order to {@code import} it, without its {@code .sou}.
 *
 * <p>The declarations are put back together as one source and handed to the parser, so what an
 * importing project sees is what the declaring project wrote, read by the same front end. What comes
 * back of the module's implementation is what its declarations cannot be read without: the helpers
 * an invariant calls, and the {@code let}s it publishes, which a reader substitutes and expands for
 * itself. Every other body stays where it was written.
 *
 * <p>Travelling as source is also what a published body's meaning rests on. A helper is read back by
 * the same rule that read it in the first place, so one whose parameter types its body settles
 * arrives with no types written and is settled again here — including one that names what a value is
 * and leaves what it holds open, which is why no type variable has to be written for it to cross.
 *
 * <p>Reading the import lines is part of reading the module and not a step after it, and so is
 * indexing what it declares. A module comes out of here with its library names already answered and
 * its declarations already indexed ({@link ReadableModule}), because both can fail and both used to
 * be left to whoever wanted them: a caller that read the module and not the import lines held one
 * whose bare names resolved against nothing in every project but the one that wrote it, and a
 * caller that indexed afterwards had a known failure arriving as a raise from inside a lookup.
 *
 * <p>Nothing here raises for an artifact this compiler will not read. Every such failure is a
 * {@link Readback.Failure}, named where it is found by the code that knows its shape, so what
 * converts is stated rather than decided by how wide a caller's catch happened to be.
 *
 * <p>One raise is turned into a failure here, the parser's, and the catch is around the parse
 * alone. The other physical way a reading fails — bytes this runtime does not read — is answered
 * as a value by {@link PublishedClasses}, which is where the bytes are and so the only place that
 * knows what went wrong with them. Nothing here reads an exception type as a statement about
 * somebody's artifact.
 */
public final class ModuleReadback {

    private ModuleReadback() {}

    /**
     * Where the code of {@code module} is written, as anything reading it back says so.
     *
     * <p>One function, because there is one answer and two callers. This is what stamps the parse,
     * and a report about a module that never got as far as being parsed — an artifact at a boundary
     * revision this compiler does not agree with, one whose declaration class is missing — has no
     * position to read a provenance off and its name is all there is. Written out at both, the two
     * agree only for as long as provenance is a module name and nothing else; the day it carries
     * where the published source is, this is the one place that learns it.
     */
    public static SourceProvenance provenanceOf(String module) {
        return new SourceProvenance.APublishedModule(module);
    }

    /**
     * Whether {@code classes} say anything at all about {@code module}, as against saying something
     * this compiler will not read.
     *
     * <p>Asked of the classes, and not by reading. Whether the path carries a name is settled by
     * whether there is a class of it with declarations on it; whether what those declarations say
     * can be read back is a further question with its own answer, and a caller that wanted only the
     * first used to get it by doing the whole reading and looking at what came out. That put every
     * way a readback can fail into the failure domain of a question that does not depend on any of
     * them — a module compiled here that also sits on the path, in a jar built by another compiler,
     * ended the compilation from a question whose whole answer is yes or no.
     */
    public static boolean carry(String module, PublishedClasses classes) {
        return switch (classes.of(declarationsClassOf(module))) {
            case PublishedClasses.Carried.NoSuchClass _ -> false;
            // Carried, and not readable. Those are the two questions this whole reading is written
            // to keep apart, and folding the second into "no such name" here would have answered
            // one of them with the other — the same collapse, at the one query that was meant not
            // to depend on the reading at all.
            case PublishedClasses.Carried.UnreadableMetadata _ -> true;
            case PublishedClasses.Carried.Declared(PublishedClasses.Declarations d) ->
                    d.module() != null;
        };
    }

    /** What {@code classes} carry for {@code moduleName}. */
    public static Readback<ReadableModule> read(String moduleName, PublishedClasses classes,
                                                LibraryNames library) {
        PublishedClasses.Declarations found;
        switch (classes.of(declarationsClassOf(moduleName))) {
            case PublishedClasses.Carried.NoSuchClass _ -> {
                return new Readback.NotReady.SaysNothing<>(moduleName);
            }
            case PublishedClasses.Carried.UnreadableMetadata _ -> {
                return unreadable(moduleName, new Readback.Failure.UnreadableMetadata());
            }
            case PublishedClasses.Carried.Declared(PublishedClasses.Declarations declared) ->
                    found = declared;
        }
        if (found.module() == null) {
            // a class this compiler put no declarations on
            return new Readback.NotReady.SaysNothing<>(moduleName);
        }
        PublishedClasses.SoutherModuleView m = found.module();
        // A member this compiler asks for and the writer did not write reads as its default. The
        // header is the one that cannot be defaulted — without it there is no module to parse — so a
        // module that carries none was written by something this compiler does not agree with,
        // whatever its number says.
        if (m.compat() != Backend.BOUNDARY_VERSION || m.header().isBlank()) {
            return unreadable(moduleName, new Readback.Failure.Incompatible(m.compiler()));
        }
        StringBuilder declarations = new StringBuilder();
        Map<String, BehaviorImplementation> implementations = new LinkedHashMap<>();
        Map<String, PublishedSignature> signaturesFrom = new LinkedHashMap<>();
        for (String type : m.types()) {
            PublishedClasses.Declarations carried;
            switch (classes.of(moduleName + "." + type)) {
                case PublishedClasses.Carried.UnreadableMetadata _ -> {
                    return unreadable(moduleName,
                            new Readback.Failure.UnreadableMetadata());
                }
                case PublishedClasses.Carried.NoSuchClass _ -> {
                    return unreadable(moduleName,
                            new Readback.Failure.DeclarationMissing(type));
                }
                case PublishedClasses.Carried.Declared(PublishedClasses.Declarations d) ->
                        carried = d;
            }
            if (carried.data() == null) {
                return unreadable(moduleName, new Readback.Failure.DeclarationMissing(type));
            }
            declarations.append('\n').append(carried.data()).append('\n');
        }
        for (String behavior : m.behaviors()) {
            PublishedClasses.Declarations carried;
            switch (classes.of(SoutherJvmAbi.nameOf(
                    new GeneratedClass.BehaviorInterface(moduleName, behavior)).binaryName())) {
                case PublishedClasses.Carried.UnreadableMetadata _ -> {
                    return unreadable(moduleName,
                            new Readback.Failure.UnreadableMetadata());
                }
                case PublishedClasses.Carried.NoSuchClass _ -> {
                    return unreadable(moduleName,
                            new Readback.Failure.DeclarationMissing(behavior));
                }
                case PublishedClasses.Carried.Declared(PublishedClasses.Declarations d) ->
                        carried = d;
            }
            if (carried.behaviorSignature() == null) {
                return unreadable(moduleName, new Readback.Failure.DeclarationMissing(behavior));
            }
            declarations.append('\n').append(carried.behaviorSignature()).append('\n');
            PublishedSignature from =
                    PublishedSignature.readingWritten(carried.behaviorSignatureFrom());
            if (from == null) {
                return unreadable(moduleName, new Readback.Failure.UnreadableMetadata());
            }
            signaturesFrom.put(behavior, from);
            BehaviorImplementation implementation;
            try {
                implementation =
                        BehaviorImplementation.readingWritten(carried.behaviorImplementation());
            } catch (IllegalArgumentException | NullPointerException e) {
                // A word this compiler does not know is metadata of its name carrying something
                // else, which is the one thing a reading here refuses over.
                return unreadable(moduleName, new Readback.Failure.UnreadableMetadata());
            }
            implementations.put(behavior, implementation);
        }
        for (String helper : m.invariantHelpers()) {
            declarations.append('\n').append(helper).append('\n');
        }
        StringBuilder source = new StringBuilder(m.header()).append('\n');
        int importsFrom = source.length();
        for (String line : m.imports()) {
            source.append(line).append('\n');
        }
        Span importLines = new Span(importsFrom, source.length());
        source.append(declarations);
        CstFrontend.ReadBack readBack;
        try {
            // Read back, not read: the text was put together here out of what the module carries, so
            // its lines are lines of nothing anybody holds. Every position it makes says so from the
            // start, and a reader here reaches the module by its name.
            readBack = CstFrontend.readBackWhatAModulePublished(source.toString(),
                    provenanceOf(moduleName));
        } catch (CompileException _) {
            // Around the parse and nothing else. A pass raises, so this is the one place a raise has
            // to be turned into a failure — and wrapping any more than the call would let something
            // else's raise arrive as a statement about this artifact.
            return unreadable(moduleName, new Readback.Failure.InvalidPublishedSyntax());
        }
        Published published = asPublished(readBack.module(), signaturesFrom);
        if (published == null) {
            // A composition's signature carrying what only a declaration writes, or a signature
            // the metadata says was declared written as stages: the two members disagree about
            // what this behavior is.
            return unreadable(moduleName, new Readback.Failure.UnreadableMetadata());
        }
        Ast.Module parsed = published.module();
        if (!parsed.name().equals(moduleName)) {
            // A reading answers about the module it was asked for. The class was found by that name
            // and the module is named by the header on it; where the two differ there is no reading
            // of this module here, whatever the class carries.
            return unreadable(moduleName, new Readback.Failure.AnotherModule(parsed.name()));
        }
        // Indexed before the import lines are read, because that is the order the two questions
        // depend on each other in: what the module declares is settled by what it wrote, and
        // whether a line may bring a name in is asked against the declarations. Read the other way
        // round, a line is held against a set of declarations this compiler has already refused.
        DeclaredNames.Index<Ast.Def> declared = Registry.indexed(parsed);
        if (!declared.refusals().isEmpty()) {
            List<Readback.DeclarationRejection> refused = declared.refusals().stream()
                    .map(ModuleReadback::asAnArtifactsRejection).toList();
            return unreadable(moduleName, new Readback.Failure.InvalidDeclarations(
                    refused.get(0), refused.subList(1, refused.size())));
        }
        // Which imports are needed is asked of the text that was parsed, passing over the import
        // lines themselves and what was written only to carry a composition through the parser.
        List<Span> passedOver = new ArrayList<>();
        passedOver.add(importLines);
        for (Region binder : published.writtenForTheParser()) {
            passedOver.add(new Span(readBack.laidOut().offsetOf(binder.start()),
                    readBack.laidOut().offsetOf(binder.end())));
        }
        Exposing.Checked checked =
                Exposing.check(withNeededImports(parsed, source.toString(), passedOver), library);
        if (!checked.refused().isEmpty()) {
            List<Readback.Exposure> crossed = checked.refused().stream()
                    .map(ModuleReadback::asAnArtifactsFailure).toList();
            return unreadable(moduleName, new Readback.Failure.InvalidExposure(
                    crossed.get(0), crossed.subList(1, crossed.size())));
        }
        // What each value it declares was settled as, which the reading of another module's value
        // rests on. A line this cannot read is metadata of its name carrying something else.
        Preserved.SettledValues answers = ValueAnswers.read(moduleName, m.valueAnswers());
        if (answers == null) {
            return unreadable(moduleName, new Readback.Failure.UnreadableMetadata());
        }
        return new Readback.Ready<>(
                new AsRead(checked.module(), declared.declarations(), declared.asDeclared(),
                        implementations, checked.claims(), readBack.laidOut(), answers));
    }

    /**
     * The only {@link ReadableModule} there is.
     *
     * <p>Package-private, and built at one statement of {@link #read}. Nothing outside this package
     * can make one, and nothing inside it does — so a value of this type is a reading that got to
     * the end, rather than a value somebody assembled that looks like one.
     */
    record AsRead(Ast.Module module, Map<String, Ast.Def> declarations,
                  java.util.List<String> asDeclared,
                  Map<String, BehaviorImplementation> behaviorImplementations,
                  java.util.List<Scoping.Claim> libraryClaims,
                  SourceLayout laidOutText,
                  Preserved.SettledValues valueAnswers) implements ReadableModule {

        /** Copied, because this is an answer a compilation remembers and an answer it remembers is
         *  a value. */
        AsRead {
            declarations = Collections.unmodifiableMap(new java.util.TreeMap<>(declarations));
            asDeclared = java.util.List.copyOf(asDeclared);
            behaviorImplementations =
                    Collections.unmodifiableMap(new LinkedHashMap<>(behaviorImplementations));
            libraryClaims = List.copyOf(libraryClaims);
        }
    }

    /**
     * {@code parsed} with each composition put back as one.
     *
     * <p>What was parsed for a composition is a declaration with the parameter names the writer made
     * up for the parser ({@link PublishedSignature#COMPOSED}). It is a composition whose stages stayed
     * behind, and is read back as that: the types it takes and what it answers, with no names. Left
     * as a declaration, every reader that asks what kind of behavior this is would answer for one
     * that declared parameters.
     *
     * <p>The parameter names it drops are still written in the text, and where they are written is
     * answered beside the module: the text is what was parsed and stays as it is, and a reading of
     * its words passes over them.
     *
     * <p>Null where the text and the metadata disagree: a composition's signature written with a
     * clause only a declaration carries, or a behavior the metadata says was declared written as
     * stages. The writer produces neither.
     */
    private static Published asPublished(Ast.Module parsed,
                                         Map<String, PublishedSignature> signaturesFrom) {
        List<Ast.BehaviorDef> behaviors = new ArrayList<>(parsed.behaviors().size());
        List<Region> writtenForTheParser = new ArrayList<>();
        for (Ast.BehaviorDef behavior : parsed.behaviors()) {
            PublishedSignature from = signaturesFrom.get(behavior.name());
            if (from == null) {
                return null;
            }
            Ast.BehaviorDef read = switch (behavior) {
                case Ast.PipeBehavior _ -> null;
                case Ast.SpecBehavior spec -> switch (from) {
                    case DECLARED -> spec;
                    case COMPOSED -> {
                        for (Ast.Param param : spec.params()) {
                            writtenForTheParser.add(param.written().region());
                        }
                        yield compositionOf(spec);
                    }
                };
            };
            if (read == null) {
                return null;
            }
            behaviors.add(read);
        }
        return new Published(new Ast.Module(parsed.name(), parsed.exposing(),
                parsed.exposedOutputs(), parsed.imports(), parsed.defs(), behaviors, parsed.fns(),
                parsed.takenOn(), parsed.examples(), parsed.fakes(), parsed.exampleFileTarget(),
                parsed.pos()), List.copyOf(writtenForTheParser));
    }

    /**
     * A module as it was published, and where its text holds syntax that is no part of any
     * declaration: the parameter names written to carry a composition's signature through the
     * parser.
     */
    private record Published(Ast.Module module, List<Region> writtenForTheParser) {}

    /** A stretch of the published text, from {@code from} up to {@code to}, in UTF-16 code units. */
    private record Span(int from, int to) {}

    /** The composition {@code written} is the published signature of, or null where it carries a
     *  clause a composition does not write. */
    private static Ast.PipeBehavior compositionOf(Ast.SpecBehavior written) {
        if (!written.constructs().isEmpty() || !written.dependsOn().isEmpty()
                || !written.ensures().isEmpty()) {
            return null;
        }
        List<Ast.RetType> takes = new ArrayList<>(written.params().size());
        for (Ast.Param param : written.params()) {
            takes.add(param.type());
        }
        return new Ast.PipeBehavior(written.written(),
                new Ast.Composition.Elsewhere(takes, written.ret()), written.pos());
    }

    private static Readback<ReadableModule> unreadable(String module, Readback.Failure why) {
        return new Readback.NotReady.Unreadable<>(module, why);
    }

    /**
     * A declaration the indexing refused, as a fact about the artifact it was found in.
     *
     * <p>The declaration goes and the node stays behind, for the reason a refused import line's
     * does: what the indexing hands back is the form it refused, and every place in that form is a
     * place in a text this reading assembled. What crosses is which declaration and which rule.
     *
     * <p>A switch over every rule there is, with nothing to fall through to. A rule added to the
     * indexing is one this boundary has to say something about, and one that reached here with
     * nothing to say would be an artifact refused for a reason nobody can name.
     */
    private static Readback.DeclarationRejection asAnArtifactsRejection(
            DeclaredNames.Refusal<Ast.Def> refusal) {
        String declaration = refusal.refused().name();
        return switch (refusal) {
            case DeclaredNames.Refusal.DeclaredTwice<Ast.Def> _ ->
                    new Readback.DeclarationRejection.DeclaredTwice(declaration);
            case DeclaredNames.Refusal.ABuiltInOptionCaseIsDeclared<Ast.Def> _ ->
                    new Readback.DeclarationRejection.BuiltInOptionCaseDeclared(declaration);
        };
    }

    /**
     * A refusal the check found, as a fact about the artifact it was found in.
     *
     * <p>The place goes here and nowhere else. A refusal carries the {@code import} line it was
     * written on, which is what lets a reader holding that source quote it; this side has no source
     * to quote and the line is in a text nobody holds, so what crosses is what happened. Left on,
     * the position this whole type exists to keep out would have arrived as an AST node instead of
     * as a diagnostic.
     *
     * <p>A switch over every refusal there is, with nothing to fall through to: a rule added to the
     * check is one this boundary has to say something about, and one that reached here with nothing
     * to say would be an artifact refused for a reason nobody can name.
     */
    private static Readback.Exposure asAnArtifactsFailure(Exposing.Refusal refusal) {
        return switch (refusal) {
            case Exposing.Refusal.NoSuchLibraryFunction r ->
                    new Readback.Exposure.NoSuchLibraryFunction(r.imp().module(), r.name());
        };
    }

    /**
     * {@code module} with the import lines its declarations do not need left out. A module's
     * {@code let} bodies are not published, so an import only they used would otherwise be
     * republished and every importing project would have to put that module on its path to read
     * declarations that never mention it (issue #138).
     *
     * <p>Needed is decided on the words of the published text rather than on the parsed
     * declarations, and a word is a word wherever it is written — in a field's type, a spread, an
     * invariant, a helper an invariant calls, an exposed composition's output. A walk over the
     * parsed forms would have to name every place a type can appear and would drop an import the day
     * one is added; a word that is written nowhere cannot be referred to by anything.
     *
     * <p>The words of every declaration, and nothing else: {@code passedOver} is where the text holds
     * something else — the import lines being decided about, and syntax written only to carry a
     * declaration through the parser, which for a published composition is the parameter names its
     * signature is written with. Those are found by where the parse put them, and the text itself is
     * read as it is.
     */
    private static Ast.Module withNeededImports(Ast.Module module, String text,
                                                List<Span> passedOver) {
        Set<String> written = new LinkedHashSet<>();
        Set<String> qualifiers = new LinkedHashSet<>();
        for (String word : words(text, passedOver)) {
            written.add(word);
            int dot = word.lastIndexOf('.');
            if (dot > 0) {
                qualifiers.add(word.substring(0, dot));
            }
        }
        List<Ast.Import> needed = new ArrayList<>();
        for (Ast.Import imp : module.imports()) {
            if (!Collections.disjoint(written, imp.names())
                    || qualifiers.contains(imp.module())
                    || (imp.alias() != null && qualifiers.contains(imp.alias()))) {
                needed.add(imp);
            }
        }
        if (needed.size() == module.imports().size()) {
            return module;
        }
        return new Ast.Module(module.name(), module.exposing(), module.exposedOutputs(), needed,
                module.defs(), module.behaviors(), module.fns(), module.takenOn(),
                module.examples(), module.fakes(), module.exampleFileTarget(), module.pos());
    }

    /**
     * Every maximal run of name characters in {@code text}, a qualified name counting as one word.
     * The dot joins a qualifier to what it qualifies, so it is part of a run; a dot that does not
     * join two names is dropped from the ends, which is what makes the spread {@code ...Common}
     * read as the name it spreads.
     *
     * <p>A run inside a string literal is a word here too: it costs an import that is kept, which is
     * what was published anyway.
     *
     * <p>What lies in {@code passedOver} is read as no part of any word, so a run ends where one
     * begins and starts again after it, and nothing on either side of it is joined into a word the
     * text does not write.
     */
    private static List<String> words(String text, List<Span> passedOver) {
        boolean[] skipped = new boolean[text.length()];
        for (Span span : passedOver) {
            for (int i = span.from(); i < span.to(); i++) {
                skipped[i] = true;
            }
        }
        List<String> words = new ArrayList<>();
        int start = -1;
        for (int i = 0; i <= text.length(); i++) {
            boolean part = i < text.length() && !skipped[i]
                    && (Character.isLetterOrDigit(text.charAt(i)) || text.charAt(i) == '_'
                            || text.charAt(i) == '.');
            if (part && start < 0) {
                start = i;
            } else if (!part && start >= 0) {
                String word = trimDots(text.substring(start, i));
                if (!word.isEmpty()) {
                    words.add(word);
                }
                start = -1;
            }
        }
        return words;
    }

    private static String trimDots(String word) {
        int from = 0;
        int to = word.length();
        while (from < to && word.charAt(from) == '.') {
            from++;
        }
        while (to > from && word.charAt(to - 1) == '.') {
            to--;
        }
        return word.substring(from, to);
    }

    /** The class a module's declarations are stamped on. */
    private static String declarationsClassOf(String module) {
        return SoutherJvmAbi.nameOf(new GeneratedClass.ModuleDeclarations(module)).binaryName();
    }
}
