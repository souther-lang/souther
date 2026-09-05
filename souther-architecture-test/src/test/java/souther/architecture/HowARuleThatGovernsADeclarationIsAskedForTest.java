package souther.architecture;

import souther.compiler.ast.Hir;
import souther.compiler.check.DerivedSymbols;
import souther.compiler.check.ExpandedClauseLookup;
import souther.compiler.check.Symbols;
import souther.test.RepositoryLayout;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.classfile.Attributes;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.reflect.AccessFlag;
import java.lang.reflect.RecordComponent;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How a caller asks for the rules that govern a declaration.
 *
 * <p>Which declarations govern one — its own and every one a spread reaches — is a walk over the
 * declarations, and it is {@code TypeOps}' walk. Two things are held of its surface, and they are
 * two because what they are about is two.
 *
 * <p><b>The walk is given a name and reads the declarations itself.</b> A caller that passed a
 * declaration node beside the world would be deciding the representation of the declaration asked
 * about while the world decided the ones under it, and nothing either of them held would say the
 * two were the same reading.
 *
 * <p><b>What a clause states is read from whatever owns that representation.</b> The settled form is
 * the derived world's, so a walk that answers with one takes {@link DerivedSymbols} and not the
 * reader that does not name a stage. The expanded form is
 * {@code ExpandedClauseLookup}'s — one question, one input, no node to fall back on — and that
 * interface holds its own answer; a rule here that demanded the derived world of it as well would
 * be reporting a walk that is already closed, by a stronger arrangement than this one.
 *
 * <p>What this does not hold is that no walk of the kind can be written anywhere else. A class
 * reaching the declarations itself could compose its own, and no reading of a signature would say
 * so. The first line against that is which methods are reachable at all, and this is the second.
 */
class HowARuleThatGovernsADeclarationIsAskedForTest {

    private static final String A_CLAUSE = internal(Hir.InvariantClause.class);
    private static final String A_DECLARATION = internal(Hir.Def.class);
    private static final String THE_DERIVED_WORLD = internal(DerivedSymbols.class);
    private static final String THE_LOOKUP = internal(ExpandedClauseLookup.class);

    /** The declaration worlds, read off the sealed interface rather than listed: a world added to it
     *  is one a walk could be handed, and these rules have to see it arrive. */
    private static final Set<String> THE_WORLDS = worlds();

    private static final Pattern NAMES_A_TYPE = Pattern.compile("L([^;<]+)[;<]");

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    private static Set<String> worlds() {
        Set<String> out = new LinkedHashSet<>();
        out.add(internal(Symbols.class));
        for (Class<?> each : Symbols.class.getPermittedSubclasses()) {
            out.add(internal(each));
        }
        return out;
    }

    /** Every declaration node, read off the sealed interface for the same reason. */
    private static Set<String> declarationNodes() {
        Set<String> out = new LinkedHashSet<>();
        out.add(A_DECLARATION);
        for (Class<?> each : Hir.Def.class.getPermittedSubclasses()) {
            out.add(internal(each));
        }
        return out;
    }

    private static String internal(Class<?> type) {
        return type.getName().replace('.', '/');
    }

    /** One method as these rules read it. Split at the parameters' close, because which half a type
     *  is named in is what is being asked: a walk is handed a world and answers with clauses. */
    private record Read(String name, String takes, String answersWith) {

        String shown() {
            return name + "(" + takes + ")" + answersWith;
        }
    }

    /**
     * The methods another class can ask this one for.
     *
     * <p>Not the public ones. What these rules are about is what a caller elsewhere may reach, and a
     * package-private method is reachable by every class beside it — the walk that answers with the
     * settled form is one of those, so a reading of the public surface alone would be a rule about a
     * set its own subject is not in. A private method is the class's own business and is held by
     * what its neighbours here do with it, which is a thing to read rather than to check.
     */
    private static List<Read> reachableMethods() {
        List<Read> out = new ArrayList<>();
        for (MethodModel method : typeOps().methods()) {
            if (method.flags().has(AccessFlag.PRIVATE) || method.flags().has(AccessFlag.SYNTHETIC)
                    || method.methodName().stringValue().startsWith("<")) {
                continue;
            }
            // The generic signature where there is one. A clause reached through a list, an
            // `Optional`, a map value or a record is a clause a caller gets, and the containers
            // erase to something naming no clause at all — so a rule read off the descriptor would
            // hold of exactly the shape nobody writes.
            String signature = method.findAttribute(Attributes.signature())
                    .map(each -> each.signature().stringValue())
                    .orElseGet(() -> method.methodType().stringValue());
            int closed = signature.lastIndexOf(')');
            out.add(new Read(method.methodName().stringValue(),
                    signature.substring(signature.indexOf('(') + 1, closed),
                    signature.substring(closed + 1)));
        }
        return out;
    }

    /** The walks: what answers with a rule of a declaration, in either representation. */
    private static List<Read> walksOverWhatGoverns() {
        List<Read> found = new ArrayList<>();
        for (Read method : reachableMethods()) {
            if (reachesAClause(method.answersWith()) && reachesOneOf(method.takes(), THE_WORLDS)) {
                found.add(method);
            }
        }
        return found;
    }

    @Test
    void aWalkOverWhatGovernsIsGivenANameAndNotADeclaration() {
        List<String> handedANode = new ArrayList<>();
        for (Read walk : walksOverWhatGoverns()) {
            if (reachesADeclaration(walk.takes())) {
                handedANode.add(walk.shown());
            }
        }

        assertEquals(List.of(), handedANode,
                "a walk over what governs a declaration reads the declarations from the world it"
                        + " was handed, so that the one asked about and the ones a spread reaches"
                        + " are one reading");
    }

    @Test
    void aWalkThatAnswersWithTheSettledFormTakesTheDerivedWorld() {
        List<String> loose = new ArrayList<>();
        for (Read walk : walksOverWhatGoverns()) {
            // What the expanded form states is the lookup's to answer, and it holds that itself.
            if (reachesOneOf(walk.takes(), Set.of(THE_LOOKUP))) {
                continue;
            }
            if (!reachesOneOf(walk.takes(), Set.of(THE_DERIVED_WORLD))) {
                loose.add(walk.shown());
            }
        }

        assertEquals(List.of(), loose,
                "the settled form of a clause is the derived world's, so a walk that answers with"
                        + " one says which world it read");
    }

    /**
     * And each rule above is about something.
     *
     * <p>Held for the two representations apart, because the rules are. The settled walk is the one
     * the derived world's rule is about and the expanded walks are the ones it passes over, so a
     * count of both together is a count that stays right while either goes to nothing — which is how
     * a rule comes to hold of an empty set and say so to nobody.
     */
    @Test
    void thereAreWalksOfEachKind() {
        List<String> settled = new ArrayList<>();
        List<String> expanded = new ArrayList<>();
        for (Read walk : walksOverWhatGoverns()) {
            (reachesOneOf(walk.takes(), Set.of(THE_LOOKUP)) ? expanded : settled).add(walk.shown());
        }

        assertFalse(settled.isEmpty(),
                "a walk here answers with the settled form, which is what the derived world's rule"
                        + " is about");
        assertFalse(expanded.isEmpty(),
                "a walk here answers with the expanded form, which that rule passes over because"
                        + " the lookup holds it");
    }

    /**
     * And a walk is found through what its answer is made of, not through what its answer is called.
     *
     * <p>The walks here answer with a value that names no clause: what a caller gets the clauses out
     * of is a record the answer holds. A reading that took the types written in the signature would
     * find none of them, and {@link #thereAreWalksOfEachKind} would be failing for that reason
     * rather than saying there is no walk — so this is held on its own.
     */
    @Test
    void aClauseInsideWhatAWalkAnswersWithIsOneThisReads() {
        List<String> namingNoClause = new ArrayList<>();
        for (Read walk : walksOverWhatGoverns()) {
            if (!walk.answersWith().contains(A_CLAUSE)) {
                namingNoClause.add(walk.shown());
            }
        }

        assertFalse(namingNoClause.isEmpty(),
                "a walk here answers with something that names no clause and holds one, which is"
                        + " what makes following a record the thing to do");
    }

    /** Held so the readings above are over the members that class writes and not over a class file
     *  that was not found: a scan of nothing reports nothing loose. */
    @Test
    void theClassTheseRulesAreAboutWasRead() {
        assertTrue(reachableMethods().size() > 1,
                "the class these rules are about was read and has a public surface");
    }

    /**
     * Whether what {@code signature} describes reaches a clause: it names one, or it names a record
     * that holds one.
     *
     * <p>Held over what a type is made of and not over what it is called. A record carrying a clause
     * hands its caller the clause, and a rule that read only the types written in the signature
     * would be answered by wrapping a walk's answer in a record — one line, and no word about the
     * reading having changed.
     */
    private static boolean reachesAClause(String signature) {
        return reachesOneOf(signature, Set.of(A_CLAUSE));
    }

    /**
     * Whether what {@code signature} describes reaches a declaration node.
     *
     * <p>Read the way the answer is read, and for the reason the answer is: a pair of a name and the
     * declaration under it, wrapped in a record, is the same thing to be handed as the two written
     * side by side. This is not a shape nobody writes — it is what a newtype layer was, and closing
     * it is half of what this file is about.
     */
    private static boolean reachesADeclaration(String signature) {
        return reachesOneOf(signature, declarationNodes());
    }

    private static boolean reachesOneOf(String signature, Set<String> wanted) {
        Matcher named = NAMES_A_TYPE.matcher(signature);
        while (named.find()) {
            if (reaches(named.group(1), wanted, new LinkedHashSet<>())) {
                return true;
            }
        }
        return false;
    }

    private static boolean reaches(String type, Set<String> wanted, Set<String> seen) {
        if (wanted.contains(type)) {
            return true;
        }
        if (!type.startsWith("souther/") || !seen.add(type)) {
            return false;
        }
        Class<?> loaded;
        try {
            loaded = Class.forName(type.replace('/', '.'), false,
                    HowARuleThatGovernsADeclarationIsAskedForTest.class.getClassLoader());
        } catch (ClassNotFoundException _) {
            return false;
        }
        if (!loaded.isRecord()) {
            return false;
        }
        for (RecordComponent component : loaded.getRecordComponents()) {
            String generic = component.getGenericSignature();
            Matcher named = NAMES_A_TYPE.matcher(
                    generic != null ? generic : component.getType().descriptorString());
            while (named.find()) {
                if (reaches(named.group(1), wanted, seen)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * The compiled class these rules read, found through the repository.
     *
     * <p>Not through {@code java.class.path}. What a module is handed there is the reactor's to
     * decide and it is not the same in every build — a module built beside this one arrives as its
     * {@code target/classes}, and one already packaged arrives as a jar — so a walk over the entries
     * is a walk over something that answers differently depending on which goal was run. What these
     * rules are about is the compiled surface of a class of this repository, and the repository is
     * where that is.
     */
    private static ClassModel typeOps() {
        for (Path module : REPOSITORY.modules()) {
            Path compiled = module.resolve("target").resolve("classes")
                    .resolve("souther/compiler/check/TypeOps.class");
            if (Files.isRegularFile(compiled)) {
                try {
                    return ClassFile.of().parse(Files.readAllBytes(compiled));
                } catch (IOException e) {
                    throw new UncheckedIOException(e);
                }
            }
        }
        throw new AssertionError("the class these rules are about was not built here");
    }
}
