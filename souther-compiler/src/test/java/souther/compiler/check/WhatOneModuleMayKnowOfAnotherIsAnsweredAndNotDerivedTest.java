package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.diag.EveryShippedMessageCatalogIsCompleteAndValidTest;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.GenericArrayType;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.lang.reflect.WildcardType;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What one module may know of another is answered by the reading of that module, and worked out
 * nowhere else.
 *
 * <p>Four walks used to work it out. Whether a module exposed a name, which behaviors it declared,
 * which of its definitions it handed over: each reader went to {@code exposing} and {@code
 * behaviors} and {@code fns} and decided for itself, and the readers disagreed. A behavior arrived
 * under an import line that had just been refused for not exposing it. A definition was published
 * to the pass that expands bodies and not to the pass that answers names. What is wrong in each
 * case is not the answer but that there was more than one place to get one.
 *
 * <p>Three rules, and this is where they are kept.
 *
 * <ol>
 *   <li>A consumer does not derive another module's settled semantic facts from its syntax or IR.
 *   <li>Semantic observations of another module are answered only by its observation.
 *   <li>Reaching another module's representation is a capability of its own, and holding it does
 *       not carry the right to decide what may be taken from there.
 * </ol>
 *
 * <p>The first two are kept by there being nothing to derive from: a reading holds no module, so a
 * reader that wanted to sort another module's declarations for itself has nothing to sort. The
 * third is kept by {@link PublishedHelper}, which is what a body is reached through and which only
 * a reading can make.
 *
 * <p>Written as checks rather than left to review because the shape is one a reviewer reads past.
 * Every one of the four walks was correct where it stood; what was wrong was only visible by
 * holding two of them side by side, and nothing in either file said the other existed.
 */
class WhatOneModuleMayKnowOfAnotherIsAnsweredAndNotDerivedTest {

    /**
     * A reading of another module hands back no module.
     *
     * <p>The whole of the first two rules, as far as a type can carry them. A reader that could
     * reach the tree could work out what it exposes, which behaviors it declares and which
     * definitions it publishes — the four walks did exactly that — and "nothing does today" is not
     * a rule. Read through the wrapping and not only at the top, because a tree inside an
     * {@code Optional} or a {@code List} is a tree the reader has.
     *
     * <p>A declaration is not a tree. Which declarations a module has is settled at the same
     * boundary and handed out whole by every registry, so answering with one gives a reader nothing
     * it did not already have a question for.
     */
    @Test
    void aReadingOfAnotherModuleHandsBackNoModule() {
        List<String> handedOver = new ArrayList<>();
        for (Method each : ModuleUniverse.InSight.Read.class.getMethods()) {
            if (each.getDeclaringClass() == Object.class) {
                continue;
            }
            for (Class<?> answered : mentioned(each.getGenericReturnType())) {
                if (answered == Ast.Module.class || answered == Hir.Module.class
                        || answered == Ast.Import.class) {
                    handedOver.add(each.getName() + " -> " + answered.getSimpleName());
                }
            }
        }
        assertEquals(List.of(), handedOver,
                "a neighbour is what was settled about it, not what it wrote");
    }

    /**
     * Deciding is asked one name at a time, and the one enumeration says what it is for.
     *
     * <p>A set handed to a reader that only had a question is a reader that can write a rule of its
     * own about what the module has. The names a report may offer are the exception and are named
     * for it: what belongs in a "did you mean" is a question about reports — how near a spelling has
     * to be, whether something unreachable is worth offering — and answered by the same method as
     * the decision, a change to either would be a change to both.
     *
     * <p>A count and not a list of which ones are allowed. A second enumeration is a decision
     * somebody should have to justify, whatever it is called.
     */
    @Test
    void oneEnumerationAndItIsTheOneForReports() {
        List<String> enumerating = new ArrayList<>();
        for (Method each : ModuleUniverse.InSight.Read.class.getMethods()) {
            if (each.getDeclaringClass() == Object.class || each.getParameterCount() > 0) {
                continue;
            }
            Class<?> answered = each.getReturnType();
            if (Collection.class.isAssignableFrom(answered) || Map.class.isAssignableFrom(answered)) {
                enumerating.add(each.getName());
            }
        }
        assertEquals(List.of("behaviorNamesToSuggest"), enumerating,
                "deciding is per name; the one enumeration is for what a report may offer");
    }

    /**
     * Nothing outside the reading can say a definition is published.
     *
     * <p>The third rule as a type. A pass that expands a published body across the boundary has to
     * hold the other module's tree, and holding it is not leave to take anything from it: the body
     * is reached by redeeming a leave, and a reading is the only thing that makes one. Left as a
     * {@code boolean} and a name, the pass would hold the tree and the name and could reach a
     * definition nothing agreed to hand over — which is how the publication rule came to be written
     * twice, once over each representation.
     *
     * <p>What is asked is where a leave is made, and not where one can be seen. A leave travels —
     * the claim that survived the contest carries it, which is what lets the reader redeem exactly
     * what it was granted — so counting the places that hand one back would count carriers, and a
     * carrier grants nothing. The constructor is private and declared inside the reading, which
     * closes it to one file; asked of the source, the places that call it number one. Package
     * boundaries would have left every class beside the reading able to write its own, and a check
     * on the shape of the API would miss a second one written next to the first.
     */
    @Test
    void onlyAReadingSaysADefinitionIsPublished() throws IOException {
        Class<?> leave = ModuleUniverse.InSight.Read.PublishedHelper.class;
        for (Constructor<?> each : leave.getDeclaredConstructors()) {
            assertTrue(Modifier.isPrivate(each.getModifiers()),
                    () -> "a leave anything beside the reading can write is granted by nobody: "
                            + each);
        }
        assertEquals(ModuleUniverse.InSight.Read.class, leave.getEnclosingClass(),
                "a leave is written by what grants it");
        List<String> minting = new ArrayList<>();
        for (Path source : EveryShippedMessageCatalogIsCompleteAndValidTest.mainSources()) {
            String text = read(source);
            int at = text.indexOf("new PublishedHelper(");
            while (at >= 0) {
                minting.add(source.getFileName().toString());
                at = text.indexOf("new PublishedHelper(", at + 1);
            }
        }
        assertEquals(List.of("ModuleUniverse.java"), minting,
                "a leave is written where publication is settled, and nowhere else");
        List<String> asking = new ArrayList<>();
        for (Path source : EveryShippedMessageCatalogIsCompleteAndValidTest.mainSources()) {
            if (source.getFileName().toString().equals("ModuleUniverse.java")) {
                continue;   // where the question is answered
            }
            if (read(source).contains(".publishedHelper(")) {
                asking.add(source.getFileName().toString());
            }
        }
        assertEquals(List.of("Scoping.java"), asking,
                "what a module offers is asked where claims are made; what an importer was left"
                        + " with is a different question and is asked of the settled answer");
    }

    /**
     * The rule that decides whether a definition is handed over is written down once.
     *
     * <p>Asked of the source, because what is wrong with two readers is not visible in either of
     * them. It was asked at both representations — of a module nothing had resolved, to answer what
     * a bare name reaches, and of a settled one, to expand a body across the boundary — and the two
     * gathered their inputs differently: one read the exposing list through the rule that drops a
     * member entry, the other read it raw, and neither asked the other.
     *
     * <p>A count of the places that reach the rule, not a list of which they are. Somewhere is
     * where a rule is applied; a second somewhere is the defect.
     */
    @Test
    void publicationIsDecidedInOnePlace() throws IOException {
        List<String> reached = new ArrayList<>();
        for (Path source : EveryShippedMessageCatalogIsCompleteAndValidTest.mainSources()) {
            String text = read(source);
            if (source.getFileName().toString().equals("HelperInliner.java")) {
                continue;   // where the rule is written
            }
            if (text.contains("publishes(")) {
                reached.add(source.getFileName().toString());
            }
        }
        assertEquals(List.of("ModuleUniverse.java"), reached,
                "publication is settled where a module becomes a reading, and asked of that");
    }

    /** Every class a type mentions, through generics and arrays, so a wrapper hides nothing. */
    private static Set<Class<?>> mentioned(Type type) {
        Set<Class<?>> found = new LinkedHashSet<>();
        collect(type, found);
        return found;
    }

    private static void collect(Type type, Set<Class<?>> found) {
        switch (type) {
            case Class<?> each -> {
                if (found.add(each) && each.isArray()) {
                    collect(each.getComponentType(), found);
                }
            }
            case ParameterizedType each -> {
                collect(each.getRawType(), found);
                for (Type argument : each.getActualTypeArguments()) {
                    collect(argument, found);
                }
            }
            case GenericArrayType each -> collect(each.getGenericComponentType(), found);
            case WildcardType each -> {
                for (Type bound : each.getUpperBounds()) {
                    collect(bound, found);
                }
            }
            default -> { }
        }
    }

    private static String read(Path source) {
        try {
            return Files.readString(source);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
