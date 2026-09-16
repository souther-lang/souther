package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.constantpool.MemberRefEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Who builds a form of the grammar that no published declaration is read back as.
 *
 * <p>A declaration travels between builds as source: what a module publishes is put back together
 * as one text and read by the parser, by scoping and by resolution, and what a crossing compares is
 * what that reading answered. The passes below resolution build forms of their own out of it, and
 * those are in the tree this compile goes on to check and emit from rather than in the one a
 * crossing is handed. A sweep over what a crossing depends on says so of the form named here, and
 * says it because somebody decided it — nothing in the grammar tells an expansion from an
 * application, and no marker or constructor says which phase makes which.
 *
 * <p>What this holds is the other half: which classes build one. A pass that begins building one is
 * a row nobody wrote, and resolution beginning to build one is the decision that sweep rests on
 * going false. What it cannot see is a class already written down here coming to run while a module
 * is read back, and that residue belongs to the decision rather than here — a call graph read off
 * these classes would answer it by working out what today's implementation happens to reach, which
 * is the account taken from somewhere other than a decision that the sweep exists to refuse.
 *
 * <p>Read off the compiled classes, as the naming of a constructor. A class that only names the
 * form — matching on one, holding one it was handed — is not building one and is not a row.
 */
class WhoMayBuildAFormNoPublishedResolutionHasTest {

    /**
     * The forms.
     *
     * <p>An expansion is a helper copied into the body that calls it, and what a module publishes
     * of a helper is the helper. A metavariable is what one application of a signature left open,
     * and it is decided or read as nothing before the elaboration that made it ends.
     */
    private static final List<String> THE_FORMS = List.of(
            "souther/compiler/ast/Hir$Expansion",
            "souther/compiler/types/Type$MetaVar");

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    /**
     * The classes that build one, and why each does.
     *
     * <p>{@code HelperInliner} is the one that makes one where none was: a call to a helper becomes
     * a copy of that helper, standing where the call stood. It runs over a module this compile is
     * checking and is no part of reading a published one.
     *
     * <p>The other three rebuild one they were handed with a part replaced, and a rewrite of an
     * expansion only ever happens where there was an expansion. {@code Hir} rewrites the tree under
     * one when a body is walked; {@code HelperNames} puts back what a function argument stands in
     * for; {@code NewtypeDesugar} replaces what it was bound with.
     *
     * <p>A metavariable is made by the two that elaborate an application: {@code Elaborator} leaves
     * one where a signature's variable is not yet decided, and {@code HelperInliner} leaves one for
     * each variable of the helper it is copying. Both run over a module this compile is checking,
     * and every one they make is decided or read as nothing before that elaboration ends.
     */
    private static final List<String> BUILDING_ONE = List.of(
            "souther/compiler/ast/Hir builds souther/compiler/ast/Hir$Expansion",
            "souther/compiler/check/Elaborator builds souther/compiler/types/Type$MetaVar",
            "souther/compiler/check/HelperInliner builds souther/compiler/ast/Hir$Expansion",
            "souther/compiler/check/HelperInliner builds souther/compiler/types/Type$MetaVar",
            "souther/compiler/check/HelperNames builds souther/compiler/ast/Hir$Expansion",
            "souther/compiler/check/NewtypeDesugar builds souther/compiler/ast/Hir$Expansion");

    @Test
    void everyClassThatBuildsOneIsWrittenDown() {
        assertEquals(BUILDING_ONE, new ArrayList<>(building()),
                "a row added here is a pass that builds a form no published declaration is read"
                        + " back as, and a sweep over what a crossing depends on stops at that form"
                        + " because no reading of a published module makes one");
    }

    /**
     * The walk reads every module's classes.
     *
     * <p>Asked of the modules the repository has and not of what a build happened to leave: a module
     * whose classes are missing is one whose calls this cannot see, and the rows from the rest would
     * match and this would pass while answering about fewer modules than it names.
     */
    @Test
    void andEveryModuleTheRepositoryHoldsWasRead() {
        assertTrue(modulesRead() > 1,
                "the classes this reads are in more than the one module that declares the form");
    }

    /** Every class naming one of the forms' constructors, as the class and what it named. */
    private static Set<String> building() {
        Set<String> found = new TreeSet<>();
        for (ClassModel model : COMPILED.all()) {
            String reading = model.thisClass().asInternalName();
            if (THE_FORMS.contains(reading)) {
                continue;
            }
            for (PoolEntry entry : model.constantPool()) {
                if (entry instanceof MemberRefEntry member
                        && THE_FORMS.contains(member.owner().name().stringValue())
                        && "<init>".equals(member.name().stringValue())) {
                    found.add(reading + " builds " + member.owner().name().stringValue());
                }
            }
        }
        return found;
    }

    private static int modulesRead() {
        int read = 0;
        for (Path module : COMPILED.modules()) {
            if (COMPILED.mainOutputOf(module).isPresent()) {
                read++;
            }
        }
        return read;
    }
}
