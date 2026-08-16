package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;
import souther.compiler.ast.WrittenName;
import souther.compiler.check.Scoping;
import souther.compiler.codegen.Backend;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;

import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A module off the class path that cannot be read because assembling its scope refused something
 * says which refusal it was, whatever kind of line or declaration made it.
 *
 * <p>Which reason a reader was given used to follow from where the claim came from. A line naming
 * the standard library is read where no other module has to be in sight, so its refusal had a name
 * and travelled; every other refusal is found with the surrounding modules in hand, on the far side
 * of a seam whose answer had no room for a reason, and became a module unreadable for nothing
 * anybody could name.
 *
 * <p>Three things are held here and each catches a different failure. That every refusal is
 * converted is the projection's switch to keep — it has nothing to fall through to, so a refusal
 * added to the assembly does not compile until this boundary says something about it. That each is
 * converted to the right fact is held by building one of each. And that the fact is still there
 * when a reader asks is held by asking the universe rather than the projection, so a reason dropped
 * between the two fails here.
 */
class EveryWayAnArtifactsImportLineCanFailIsNamedTest {

    /**
     * Every refusal the assembly can make is named as the kind of fact it is about.
     *
     * <p>Neither the arms nor what each is named as is written out. Both are read off the refusal:
     * that there are these and no others comes from the type, and which of the two facts each is
     * comes from what it carries — a refusal about an import line carries the line, which is what
     * lets a reader with the source quote it, and one about a declaration carries the declaration.
     * A table written out here would be a copy of the projection's, and an arm filed under the
     * wrong one would agree with the copy.
     */
    @Test
    void everyRefusalTheAssemblyCanMakeIsNamedAsWhatItIsAbout() {
        Map<Class<?>, Readback.Failure> named = new LinkedHashMap<>();
        for (Scoping.Refusal refusal : eachRefusal()) {
            named.put(refusal.getClass(), ScopeRefusals.of(List.of(refusal)));
        }

        assertEquals(Set.of(Scoping.Refusal.class.getPermittedSubclasses()), named.keySet(),
                "every refusal assembling a scope can make is one this boundary names");
        named.forEach((refusal, fact) -> {
            Class<? extends Readback.Failure> kind = writtenOnAnImportLine(refusal)
                    ? Readback.Failure.InvalidExposure.class
                    : Readback.Failure.InvalidDeclarations.class;
            assertInstanceOf(kind, fact,
                    refusal.getSimpleName() + " is named as the other kind of fact");
        });
    }

    /** Whether the refusal is about an import line, which is what carrying one says of it. */
    private static boolean writtenOnAnImportLine(Class<?> refusal) {
        for (RecordComponent part : refusal.getRecordComponents()) {
            if (part.getType() == Ast.Import.class) {
                return true;
            }
        }
        return false;
    }

    /** A refused line is said as a line, and a refused declaration as a declaration. */
    @Test
    void aRefusedLineIsSaidAsALineAndARefusedDeclarationAsADeclaration() {
        assertEquals(new Readback.Failure.InvalidExposure(
                        new Readback.Exposure.NotExposed("lib.money", "Amount"), List.of()),
                ScopeRefusals.of(List.of(new Scoping.Refusal.NotExposed(line("lib.money"),
                        "Amount"))));
        assertEquals(new Readback.Failure.InvalidDeclarations(
                        new Readback.DeclarationRejection.TakesTheLibraryQualifier("List"),
                        List.of()),
                ScopeRefusals.of(List.of(new Scoping.Refusal.TakesTheLibraryQualifier(
                        new Ast.UnitData("List", "app.order", null)))));
    }

    /**
     * What it declares is answered before what its lines could not do, where both were refused.
     *
     * <p>Not the order they were found in — they come out of one assembly and have no order between
     * them. It is the order the two questions depend on each other in: what a module declares is
     * settled by what it wrote, and whether a line may bring a name in is asked against those
     * declarations, so a reader told about the line has been told about a line held against a set of
     * declarations this compiler has already refused.
     */
    @Test
    void whatItDeclaresIsAnsweredBeforeWhatItsLinesCouldNotDo() {
        List<Scoping.Refusal> both = List.of(
                new Scoping.Refusal.NotExposed(line("lib.money"), "Amount"),
                new Scoping.Refusal.TakesTheLibraryQualifier(
                        new Ast.UnitData("List", "app.order", null)));

        assertInstanceOf(Readback.Failure.InvalidDeclarations.class, ScopeRefusals.of(both),
                "the line was refused first and the declarations are still answered first");
    }

    /** A line naming a module these classes do not carry. */
    @Test
    void aLineNamingAModuleTheseClassesDoNotCarry() {
        assertEquals(new Readback.Exposure.NoSuchModule("lib.money"),
                theLine(published(Map.of("app.order", importing(
                        List.of("import lib.money ( Amount )"),
                        Map.of("Line", "data Line = { amount: Amount }"))))));
    }

    /** A line asking for a name the module it names does not expose. */
    @Test
    void aLineAskingForWhatIsNotExposed() {
        assertEquals(new Readback.Exposure.NotExposed("lib.money", "Amount"),
                theLine(published(Map.of(
                        "lib.money", exposing("Other", Map.of("Amount", "data Amount = Decimal")),
                        "app.order", importing(List.of("import lib.money ( Amount )"),
                                Map.of("Line", "data Line = { amount: Amount }"))))));
    }

    /** A line asking for a name the module exposes and does not declare. */
    @Test
    void aLineAskingForWhatIsExposedAndNotDeclared() {
        assertEquals(new Readback.Exposure.NoSuchName("lib.money", "Amount"),
                theLine(published(Map.of(
                        "lib.money", exposing("Amount", Map.of()),
                        "app.order", importing(List.of("import lib.money ( Amount )"),
                                Map.of("Line", "data Line = { amount: Amount }"))))));
    }

    /** Two of its lines taking one alias. */
    @Test
    void twoLinesTakingOneAlias() {
        assertEquals(new Readback.Exposure.AliasTaken("lib.other", "m", "lib.money"),
                theLine(published(Map.of(
                        "lib.money", exposing("Amount", Map.of("Amount", "data Amount = Decimal")),
                        "lib.other", exposing("Amount", Map.of("Amount", "data Amount = Int")),
                        "app.order", importing(
                                List.of("import lib.money as m", "import lib.other as m"),
                                Map.of("Line", "data Line = { amount: m.Amount }"))))));
    }

    /** Two of its lines bringing one bare name in. */
    @Test
    void twoLinesBringingOneNameIn() {
        assertEquals(new Readback.Exposure.BroughtTwice("lib.other", "Amount", "lib.money"),
                theLine(published(Map.of(
                        "lib.money", exposing("Amount", Map.of("Amount", "data Amount = Decimal")),
                        "lib.other", exposing("Amount", Map.of("Amount", "data Amount = Int")),
                        "app.order", importing(List.of("import lib.money ( Amount )",
                                        "import lib.other ( Amount )"),
                                Map.of("Line", "data Line = { amount: Amount }"))))));
    }

    /** A line bringing in a name the module declares itself. */
    @Test
    void aLineBringingInWhatItDeclaresItself() {
        assertEquals(new Readback.Exposure.CollidesWithADeclaration("lib.money", "Amount"),
                theLine(published(Map.of(
                        "lib.money", exposing("Amount", Map.of("Amount", "data Amount = Decimal")),
                        "app.order", importing(List.of("import lib.money ( Amount )"),
                                Map.of("Amount", "data Amount = Int"))))));
    }

    /** A declaration taking a standard-library qualifier, which is no module's to shadow. */
    @Test
    void aDeclarationTakingTheLibraryQualifier() {
        assertEquals(new Readback.DeclarationRejection.TakesTheLibraryQualifier("List"),
                theDeclaration(published(Map.of("app.order",
                        importing(List.of(), Map.of("List", "data List = String"))))));
    }

    /** The line a reading was refused for, asked of the universe rather than of the projection. */
    private static Readback.Exposure theLine(PublishedClasses classes) {
        return assertInstanceOf(Readback.Failure.InvalidExposure.class, refusalOf(classes),
                "an import line that could not do its job").first();
    }

    /** The declaration a reading was refused for, asked the same way. */
    private static Readback.DeclarationRejection theDeclaration(PublishedClasses classes) {
        return assertInstanceOf(Readback.Failure.InvalidDeclarations.class, refusalOf(classes),
                "a declaration one module may not have").first();
    }

    /** Why {@code app.order} could not be read, as the universe answers it. */
    private static Readback.Failure refusalOf(PublishedClasses classes) {
        return assertInstanceOf(Readback.NotReady.Unreadable.class,
                PublishedUniverse.of(classes).resolved("app.order"),
                "the module is carried and this compiler will not read it").why();
    }

    /** One of each refusal, built as the assembly builds them. */
    private static List<Scoping.Refusal> eachRefusal() {
        Ast.Import money = line("lib.money");
        Ast.Import other = line("lib.other");
        List<Scoping.Refusal> each = new ArrayList<>();
        each.add(new Scoping.Refusal.NoSuchModule(money));
        each.add(new Scoping.Refusal.NotExposed(money, "Amount"));
        each.add(new Scoping.Refusal.NoSuchName(money, "Amount"));
        each.add(new Scoping.Refusal.AliasTaken(other, "lib.money"));
        each.add(new Scoping.Refusal.BroughtTwice(other, "Amount", money));
        each.add(new Scoping.Refusal.CollidesWithADeclaration(money, "Amount"));
        each.add(new Scoping.Refusal.TakesTheLibraryQualifier(
                new Ast.UnitData("List", "app.order", null)));
        each.add(new Scoping.Refusal.ALetAndADataShareASpelling(
                new Ast.FnDef(WrittenName.synthetic("amount", null), "app.order", List.of(),
                        null, null, null)));
        return each;
    }

    private static Ast.Import line(String module) {
        return new Ast.Import(module, "m", List.of(new Ast.ImportedName("Amount", null)), null);
    }

    /** The classes of a set of published modules, each stamped as another build would stamp it. */
    private static PublishedClasses published(Map<String, Module> modules) {
        Map<String, PublishedClasses.Declarations> classes = new LinkedHashMap<>();
        modules.forEach((name, module) -> {
            // Asked rather than spelled: which class a module's declarations are stamped on is the
            // ABI's to say, and a fixture that wrote the name out would be a second spelling of it.
            classes.put(SoutherJvmAbi.nameOf(
                            new GeneratedClass.ModuleDeclarations(name)).binaryName(),
                    new PublishedClasses.Declarations(
                    new PublishedClasses.SoutherModuleView(Backend.BOUNDARY_VERSION,
                            "another build",
                            "module " + name + " exposing ( " + module.exposed() + " )",
                            module.imports(), List.copyOf(module.declarations().keySet()),
                            List.of(), List.of()),
                    null, null, null));
            module.declarations().forEach((declared, text) -> classes.put(name + "." + declared,
                    new PublishedClasses.Declarations(null, text, null, null)));
        });
        return name -> PublishedClasses.carrying(classes.get(name));
    }

    /** A module whose lines are what is being read, exposing everything it declares. */
    private static Module importing(List<String> imports, Map<String, String> declarations) {
        return new Module(String.join(", ", declarations.keySet()), imports, declarations);
    }

    /** One that exposes a name of its own choosing, which is how a module comes to expose what it
     *  does not declare and to declare what it does not expose. */
    private static Module exposing(String exposed, Map<String, String> declarations) {
        return new Module(exposed, List.of(), declarations);
    }

    /** A module as it was published: what its header exposes, its import lines, and the text of
     *  each declaration. */
    private record Module(String exposed, List<String> imports, Map<String, String> declarations) {}
}
