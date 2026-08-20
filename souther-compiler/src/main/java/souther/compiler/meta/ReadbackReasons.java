package souther.compiler.meta;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.ModuleMessage;

import java.util.List;

/**
 * What is said about an artifact this compiler will not read.
 *
 * <p>One sentence per failure and one place they are written, because the fact is the same fact
 * wherever it is read. Two readers have one: a compilation says it about a module its path carries,
 * and a run holding an answer's declarations to the module being evaluated says it about the
 * classes that answer brought. Written at each of them, the two would be one rule stated twice and
 * would come apart the day a failure is added to one switch and not the other — which is the shape
 * this whole boundary exists to keep out.
 *
 * <p>What differs between the readers is the report around it, and that stays theirs. Which module
 * the sentence is about, what is said as the report and what is said under it, and what there is to
 * do about it are each the reader's; this is only the reason.
 *
 * <p>A switch over every failure there is, with nothing to fall through to. A failure added later
 * is one this has to have a sentence for, and one that reached here with nothing to say would be an
 * artifact refused for a reason nobody can name.
 */
public final class ReadbackReasons {

    private ReadbackReasons() {}

    /**
     * {@code said} with the sentence for {@code why} noted under it.
     *
     * <p>Written onto the report rather than answered as a message, because a note is a message in
     * the role of being said alongside a subject and the two travel together
     * ({@link souther.compiler.diag.msg.Supporting}).
     */
    public static Diagnostic.Builder said(Diagnostic.Builder said, Readback.Failure why) {
        return switch (why) {
            case Readback.Failure.Incompatible(String by) ->
                    said.hint(new ModuleMessage.ItWasBuiltBy(by));
            case Readback.Failure.DeclarationMissing(String declaration) ->
                    said.hint(new ModuleMessage.AClassItSaysItDeclaresIsNotOnThePath(declaration));
            case Readback.Failure.UnreadableMetadata _ ->
                    said.hint(new ModuleMessage.ItsMetadataCannotBeReadHere());
            case Readback.Failure.AnotherModule(String named) ->
                    said.hint(new ModuleMessage.ItDeclaresAnotherModule(named));
            case Readback.Failure.InvalidPublishedSyntax _ ->
                    said.hint(new ModuleMessage.WhatItPublishedIsNotSourceThisCompilerParses());
            case Readback.Failure.UnresolvedPublishedNames _ ->
                    said.hint(new ModuleMessage.ANameItPublishedReachesNothingHere());
            // The module the line names, and not which of the ways the line failed. Which rule a
            // line broke is the publishing project's to see in its own build; what a reader here
            // has to go on is which module the line reaches for, since that is what their own path
            // or the answer's is short of.
            case Readback.Failure.InvalidExposure(Readback.Exposure line, List<Readback.Exposure> _) ->
                    said.hint(new ModuleMessage.AnImportLineOfItsCannotBeReadHere(line.from()));
            case Readback.Failure.InvalidDeclarations(
                    Readback.DeclarationRejection first, List<Readback.DeclarationRejection> _) ->
                    said.hint(new ModuleMessage.ADeclarationOfItsCannotBeReadHere(
                            first.declaration()));
        };
    }
}
