package souther.compiler.meta;

import souther.compiler.conformance.RepositoryModels;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.LinkageProjection;
import souther.compiler.jvm.LinkageRecord;
import souther.compiler.jvm.LinkageTarget;
import souther.compiler.jvm.DecoderKind;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.types.TypeSymbols;
import souther.test.ClosedWorldContract;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.constantpool.ClassEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every class of another module that a module's classes name is one of a declaration the module
 * records it was built against.
 *
 * <p>One direction only, and on purpose. A class can depend on another module's declaration without
 * naming any class of it — one holding a behavior of one input keeps it as the runtime's unary
 * {@code Behavior} — so what a module records is read where a fact is read, and that half is held by
 * the regressions that change such a fact and see the module refused. What is held here is the half
 * a class file can show: a name in a constant pool that nothing recorded would be a link site the
 * recording missed.
 *
 * <p>Over every model this repository carries, as they are compiled once for the JVM that asks
 * ({@link RepositoryModels}), and a fixture beside them that reaches another
 * module in each of the ways a class can: calling a behavior by name, building a stage, holding a
 * dependency, reading a field, reading a published value, taking an answer apart through a bridge
 * case.
 */
@ClosedWorldContract
class EveryClassOfAnotherModuleAClassNamesIsOneItRecordsReadingTest {

    private static final List<String> REACHING_EVERY_WAY = List.of("""
            module lib.c exposing ( Money, Late, rate, twice, step : Int, limit, pick )
            data Money = { amount: Int }
            data Late
            behavior rate : (n: Int, m: Int) -> Int
            behavior twice : (n: Int) -> Int
            let twice (n) = n + n
            behavior double : (n: Int) -> Int
            let double (n) = n + n
            behavior step = twice >-> double
            let limit = List.length([1, 2, 3])
            behavior pick : (n: Int) -> Int | Late
            let pick (n) = if n > 0 then n else Late
            """, """
            module lib.b exposing ( read, use, again : Int, capped, charged, chosen )
            import lib.c ( Money, Late, rate, twice, step, limit, pick )
            behavior read : (m: Money) -> Int
            let read (m) = m.amount
            behavior use : (n: Int) -> Int
            let use (n) = twice(n)
            behavior again = step >-> twice
            behavior capped : (n: Int) -> Int
            let capped (n) = n + limit
            behavior charged : (n: Int) -> Int depends on rate
            let charged (n, rate) = rate(n, n)
            behavior chosen : (n: Int) -> Int
            let chosen (n) = match pick(n) with
              | Int as i -> i
              | Late -> 0
            """);

    @Test
    void everyClassOfAnotherModuleNamedIsOfADeclarationRecordedAsRead() {
        List<String> unrecorded = new ArrayList<>();
        int checked = 0;
        Compilation fixture = Compilation.ofSources(REACHING_EVERY_WAY, ModulePath.of(Map.of()));
        List<Compilation> compilations = new ArrayList<>(List.of(fixture));
        compilations.addAll(RepositoryModels.all());
        for (Compilation compilation : compilations) {
            Map<String, Map<String, ClassFileImage>> byModule = new LinkedHashMap<>();
            Map<String, ClassFileImage> all = new LinkedHashMap<>();
            for (String module : compilation.modules()) {
                Map<String, ClassFileImage> classes =
                        compilation.db().ask(new Output.Classes(module)).value();
                if (classes != null) {
                    byModule.put(module, classes);
                    all.putAll(classes);
                }
            }
            if (compilation == fixture) {
                assertEquals(Set.of("lib.b", "lib.c"), byModule.keySet(),
                        () -> "the fixture compiles, or it reaches nothing: "
                                + compilation.db().allReports().stream()
                                        .map(f -> f.report().diagnostic().code() + " "
                                                + f.report().diagnostic().said())
                                        .toList());
            }
            PublishedClasses published = ModulePath.of(all).declarations();
            for (Map.Entry<String, Map<String, ClassFileImage>> module : byModule.entrySet()) {
                Set<String> covered = covered(module.getKey(), published);
                for (Map.Entry<String, ClassFileImage> clazz : module.getValue().entrySet()) {
                    for (String named : classesNamed(clazz.getValue())) {
                        String owner = moduleOf(named, byModule.keySet());
                        if (owner == null || owner.equals(module.getKey())) {
                            continue;
                        }
                        checked++;
                        if (!covered.contains(named)) {
                            unrecorded.add(clazz.getKey() + " names " + named);
                        }
                    }
                }
            }
        }

        assertTrue(checked > 0, "no class named a class of another module, so nothing was held");
        assertEquals(List.of(), unrecorded,
                "a class names a class of another module no recorded declaration accounts for");
    }

    /**
     * The binary names of every class a declaration {@code module} records reading accounts for:
     * the classes its generated names give, and every class a recorded fact names.
     */
    private static Set<String> covered(String module, PublishedClasses published) {
        if (!(published.of(SoutherJvmAbi.nameOf(
                        new GeneratedClass.ModuleDeclarations(module)).binaryName())
                instanceof PublishedClasses.Carried.Declared(PublishedClasses.Declarations d))) {
            throw new AssertionError(module + " carries no module declarations");
        }
        Map<LinkageTarget, LinkageRecord> requires =
                PublishedLinkages.read(d.module().requiredLinkages());
        Set<String> out = new LinkedHashSet<>();
        requires.forEach((target, record) -> {
            for (GeneratedClass generated : classesOf(target)) {
                out.add(SoutherJvmAbi.nameOf(generated).binaryName());
            }
            for (LinkageProjection.Fact fact : record.facts()) {
                Matcher m = DESCRIPTOR.matcher(fact.value());
                while (m.find()) {
                    out.add(m.group(1).replace('/', '.'));
                }
            }
        });
        return out;
    }

    private static final Pattern DESCRIPTOR = Pattern.compile("L([^;()\\[]+);");

    /** The classes this compiler generates for {@code target}, by its naming rules. */
    private static List<GeneratedClass> classesOf(LinkageTarget target) {
        return switch (target) {
            case LinkageTarget.Data data -> {
                GeneratedClass.Value value =
                        new GeneratedClass.Value(TypeSymbols.declared(data.key()));
                List<GeneratedClass> out = new ArrayList<>(List.of(value,
                        new GeneratedClass.Encoder(value), new GeneratedClass.Ctfe(value)));
                for (DecoderKind kind : DecoderKind.values()) {
                    out.add(new GeneratedClass.Decoder(value, kind));
                }
                yield out;
            }
            case LinkageTarget.Behavior behavior -> {
                GeneratedClass.BehaviorInterface declared = new GeneratedClass.BehaviorInterface(
                        behavior.module(), behavior.name());
                GeneratedClass.BehaviorResult result = new GeneratedClass.BehaviorResult(
                        behavior.module(), behavior.name());
                yield List.of(declared, new GeneratedClass.BehaviorImpl(behavior.module(),
                                behavior.name()), result, new GeneratedClass.Encoder(result),
                        new GeneratedClass.Ensures(declared));
            }
            case LinkageTarget.Value value -> List.of(new GeneratedClass.Values(value.module()));
        };
    }

    /** Every class {@code image}'s constant pool names, by its binary name. */
    private static Set<String> classesNamed(ClassFileImage image) {
        ClassModel model = ClassFile.of().parse(image.bytes());
        Set<String> out = new LinkedHashSet<>();
        for (PoolEntry entry : model.constantPool()) {
            if (entry instanceof ClassEntry named) {
                String internal = named.asInternalName();
                Matcher element = DESCRIPTOR.matcher(internal);
                out.add(internal.startsWith("[") && element.find()
                        ? element.group(1).replace('/', '.') : internal.replace('/', '.'));
            }
        }
        return out;
    }

    /** The module among {@code modules} whose package {@code binaryName} is in, or null. */
    private static String moduleOf(String binaryName, Set<String> modules) {
        int dot = binaryName.lastIndexOf('.');
        String pkg = dot < 0 ? "" : binaryName.substring(0, dot);
        return modules.contains(pkg) ? pkg : null;
    }
}
