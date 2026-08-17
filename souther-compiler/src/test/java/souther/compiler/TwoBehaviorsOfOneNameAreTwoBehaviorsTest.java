package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Sig;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.Output;
import souther.compiler.types.ValueName;

import java.lang.classfile.ClassFile;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior is the module that declares it and its name, so one name in two modules is two
 * behaviors — and a module may reach both.
 *
 * <p>What made this worth writing down is that the two used to be one entry in every table below
 * the resolver, keyed by the name this module writes. Which of them the entry was fell to the order
 * they were written in, so the same model compiled to a different program depending on where a
 * declaration sat: a composition typed against a behavior nobody named, a class file emitted under
 * a name it did not declare, an injection demanded that the model never asked for.
 *
 * <p>The rows below are the ways the two can meet — declared here or reached through a module,
 * constructed or injected — with what each is asked of read off the tables the check and the
 * emitter read, rather than off a diagnostic that happens to be silent.
 */
class TwoBehaviorsOfOneNameAreTwoBehaviorsTest {

    /** A module declaring `f`, with a body, and the types around it. */
    private static final String THEIRS = """
            module app.a exposing ( In, Mid, f )
            data In = { n: Int }
            data Mid = { n: Int }
            behavior f : (i: In) -> Mid constructs Mid
            let f (i) = Mid { n = i.n }
            """;

    /** A second module declaring `f`, so two foreign ones can meet. */
    private static final String ALSO = """
            module app.b exposing ( In, Mid, f )
            data In = { n: Int }
            data Mid = { n: Int }
            behavior f : (i: In) -> Mid constructs Mid
            let f (i) = Mid { n = i.n * 2 }
            """;

    /** Every diagnostic a compile of {@code sources} reports, as its code. */
    private static List<String> reported(String... sources) {
        Compilation compilation = Compilation.ofSources(List.of(sources), ModulePath.EMPTY);
        compilation.answerEverything();
        List<String> codes = new ArrayList<>();
        for (Db.Found found : compilation.db().allReports()) {
            codes.add(found.report().diagnostic().code());
        }
        return codes;
    }

    private static Compilation compiled(String... sources) {
        Compilation compilation = Compilation.ofSources(List.of(sources), ModulePath.EMPTY);
        compilation.answerEverything();
        return compilation;
    }

    /**
     * A behavior this module declares and one it reaches through its module, sharing a name.
     *
     * <p>The composition names both. Typed by the spelling, the module's own answered for the
     * stage that named the other, and the types disagreed (E1701) on a model that is right.
     */
    @Test
    void oneDeclaredHereAndOneReachedThroughItsModule() {
        String own = """
                module app.own exposing ( Out, flow : Out )
                data Out = { n: Int }
                behavior f : (m: app.a.Mid) -> Out constructs Out
                let f (m) = Out { n = m.n }
                behavior flow = app.a.f >-> f
                """;
        assertEquals(List.of(), reported(THEIRS, own));

        Map<ValueName.Behavior, Sig> reachable =
                compiled(THEIRS, own).db().ask(new Bodies.Reachable("app.own")).value();
        assertEquals("(In) -> Mid",
                shown(reachable.get(new ValueName.Behavior("app.a", "f"))),
                "the one another module declares");
        assertEquals("(Mid) -> Out",
                shown(reachable.get(new ValueName.Behavior("app.own", "f"))),
                "and this module's own, which the composition names second");
    }

    /**
     * The module's own is an injection target and the one it reaches is constructed.
     *
     * <p>The silent half of this defect. Nothing is reported either way, and what came apart was
     * the output: the composition demanded an injection the model never asked for, and the class
     * emitted for the module's own `f` declared another module's.
     */
    @Test
    void oneInjectedHereAndOneConstructedElsewhere() {
        String own = """
                module app.own exposing ( Out, f, flow : Out )
                data Out = { n: Int }
                behavior f : (i: app.a.In) -> app.a.Mid
                behavior g : (m: app.a.Mid) -> Out constructs Out
                let g (m) = Out { n = m.n }
                behavior flow = app.a.f >-> g
                """;
        assertEquals(List.of(), reported(THEIRS, own));

        Compilation c = compiled(THEIRS, own);
        // `app.a.f` is built where it is declared, so this composition requires nothing injected.
        assertEquals(List.of(), c.db().ask(new Bodies.Requirements("app.own")).value().get("flow"));
        Map<String, byte[]> classes = c.db().ask(new Output.Classes("app.own")).value();
        assertTrue(classes.containsKey("app.own.F"), classes.keySet().toString());
        assertEquals("app.own.F", declaredBy(classes.get("app.own.F")));
    }

    /** And the other way round: the module's own is built here and the one it reaches is injected
     *  where it is declared, so this composition holds a field for that one alone. */
    @Test
    void oneConstructedHereAndOneInjectedElsewhere() {
        String theirs = """
                module app.a exposing ( In, Mid, f )
                data In = { n: Int }
                data Mid = { n: Int }
                behavior f : (i: In) -> Mid
                """;
        String own = """
                module app.own exposing ( Out, f, flow : Out )
                data Out = { n: Int }
                behavior f : (m: app.a.Mid) -> Out constructs Out
                let f (m) = Out { n = m.n }
                behavior flow = app.a.f >-> f
                """;
        assertEquals(List.of(), reported(theirs, own));

        Compilation c = compiled(theirs, own);
        assertEquals(List.of(new ValueName.Behavior("app.a", "f")),
                dependenciesOf(c, "app.own", "flow"));
    }

    /** Two behaviors of one name, both reached through their modules, in one composition each. */
    @Test
    void twoReachedThroughTheirModules() {
        String own = """
                module app.own exposing ( Out, fromA : Out, fromB : Out )
                data Out = { n: Int }
                behavior plusA : (m: app.a.Mid) -> Out constructs Out
                let plusA (m) = Out { n = m.n }
                behavior plusB : (m: app.b.Mid) -> Out constructs Out
                let plusB (m) = Out { n = m.n }
                behavior fromA = app.a.f >-> plusA
                behavior fromB = app.b.f >-> plusB
                """;
        assertEquals(List.of(), reported(THEIRS, ALSO, own));
    }

    /**
     * One composition requiring two injected behaviors of one name, from two modules.
     *
     * <p>Both are held in fields of the same generated class. What a field is called is that
     * class's own business, so two dependencies of one name are two fields and neither answers for
     * the other.
     */
    @Test
    void oneCompositionRequiringTwoInjectedOfOneName() {
        String a = """
                module app.a exposing ( In, Mid, f )
                data In = { n: Int }
                data Mid = { n: Int }
                behavior f : (i: In) -> Mid
                """;
        String b = """
                module app.b exposing ( Mid, Out, f )
                data Mid = { n: Int }
                data Out = { n: Int }
                behavior f : (m: app.a.Mid) -> Out
                """;
        String own = """
                module app.own exposing ( flow : app.b.Out )
                behavior flow = app.a.f >-> app.b.f
                """;
        assertEquals(List.of(), reported(a, b, own));

        Compilation c = compiled(a, b, own);
        assertEquals(List.of(new ValueName.Behavior("app.a", "f"),
                        new ValueName.Behavior("app.b", "f")),
                dependenciesOf(c, "app.own", "flow"),
                "one requirement each, in the order the stages name them");
        Map<String, byte[]> classes = c.db().ask(new Output.Classes("app.own")).value();
        List<String> fields = fieldNames(classes.get("app.own.Flow$Impl"));
        assertEquals(2, fields.size(), "two dependencies, two fields: " + fields);
        assertEquals(2, Set.copyOf(fields).size(),
                "and two names — a field name is the class's own, so one name cannot answer for"
                        + " both: " + fields);
    }

    /** One behavior reached twice — once bare through an import line, once through its module — is
     *  one requirement, because it is one behavior. */
    @Test
    void oneBehaviorReachedBothWaysIsOneRequirement() {
        String theirs = """
                module app.a exposing ( In, Mid, f )
                data In = { n: Int }
                data Mid = { n: Int }
                behavior f : (i: In) -> Mid
                """;
        String own = """
                module app.own exposing ( Out, one : Out, two : Out )
                import app.a ( f )
                data Out = { n: Int }
                behavior plus : (m: app.a.Mid) -> Out constructs Out
                let plus (m) = Out { n = m.n }
                behavior one = f >-> plus
                behavior two = app.a.f >-> plus
                """;
        assertEquals(List.of(), reported(theirs, own));

        Compilation c = compiled(theirs, own);
        assertEquals(List.of(new ValueName.Behavior("app.a", "f")),
                dependenciesOf(c, "app.own", "one"));
        assertEquals(List.of(new ValueName.Behavior("app.a", "f")),
                dependenciesOf(c, "app.own", "two"));
    }

    /** A composition spliced into another still names the behaviors it names, and a behavior that
     *  reaches itself through one of them is still refused (E1608). */
    @Test
    void aNestedCompositionKeepsWhatItsStagesName() {
        String own = """
                module app.own exposing ( Out, half : app.a.Mid, whole : Out )
                data Out = { n: Int }
                behavior f : (m: app.a.Mid) -> app.a.Mid constructs app.a.Mid
                behavior plus : (m: app.a.Mid) -> Out constructs Out
                let plus (m) = Out { n = m.n }
                behavior half = app.a.f >-> f
                behavior whole = half >-> plus
                """;
        Compilation c = compiled(THEIRS, own);
        // `f` here is an injection target, and the nested composition carries it into `whole`.
        assertEquals(List.of(new ValueName.Behavior("app.own", "f")),
                dependenciesOf(c, "app.own", "whole"),
                "the splice carries the behavior the inner composition names, not a name");
    }

    /**
     * The one another module declares is read back off the class path rather than compiled here.
     *
     * <p>The other side of the seam. A published module's behaviors are put back together from what
     * its classes carry, and what comes back is a declaration of that module — so a name this
     * module also declares is still two behaviors, and the composition is typed against the one it
     * names.
     */
    @Test
    void oneDeclaredHereAndOneReadBackFromTheClassPath() {
        Map<String, byte[]> published = Compiler.compile(THEIRS);
        String own = """
                module app.own exposing ( Out, flow : Out )
                data Out = { n: Int }
                behavior f : (m: app.a.Mid) -> Out constructs Out
                let f (m) = Out { n = m.n }
                behavior flow = app.a.f >-> f
                """;
        Compilation c = Compilation.ofSources(List.of(own), published::get);
        c.answerEverything();
        List<String> codes = new ArrayList<>();
        for (Db.Found found : c.db().allReports()) {
            codes.add(found.report().diagnostic().code());
        }
        assertEquals(List.of(), codes);

        Map<ValueName.Behavior, Sig> reachable = c.db().ask(new Bodies.Reachable("app.own")).value();
        assertTrue(reachable.containsKey(new ValueName.Behavior("app.a", "f")),
                "the one read back off the path: " + reachable.keySet());
        assertTrue(reachable.containsKey(new ValueName.Behavior("app.own", "f")),
                "and this module's own: " + reachable.keySet());
    }

    /** What the module requires to build {@code behavior}, in order. */
    private static List<ValueName.Behavior> dependenciesOf(Compilation c, String module,
                                                           String behavior) {
        return souther.compiler.check.Requirements.names(
                c.db().ask(new Bodies.Requirements(module)).value().get(behavior));
    }

    private static String shown(Sig sig) {
        List<String> ins = new ArrayList<>();
        sig.inputTypes().forEach(t -> ins.add(souther.compiler.types.Type.show(t)));
        return "(" + String.join(", ", ins) + ") -> "
                + souther.compiler.types.Type.show(sig.outputType());
    }

    /** The class the bytes declare themselves to be. */
    private static String declaredBy(byte[] bytes) {
        return ClassFile.of().parse(bytes).thisClass().asInternalName().replace('/', '.');
    }

    private static List<String> fieldNames(byte[] bytes) {
        List<String> names = new ArrayList<>();
        ClassFile.of().parse(bytes).fields().forEach(f -> names.add(f.fieldName().stringValue()));
        return names;
    }
}
