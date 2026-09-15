package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.ast.RowPosition;
import souther.compiler.ast.WrittenName;
import souther.compiler.diag.QuotedFrom;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ValueName;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every record a published declaration is made of is one {@link DeclarationAgreement} has decided
 * about.
 *
 * <p>The comparison walks a form's components when it has nothing else to say about it, which is
 * right for a form of the grammar and is a default for everything else. A record the compiler puts
 * beside a declaration to say something about itself — which pass rewrote a node, what a coverage
 * point was numbered as — joins the comparison the day it is added, and two builds that mean the
 * same thing start disagreeing over it. Nothing says so: the language still compiles, every test
 * still passes, and what changed is what two builds are held to.
 *
 * <p>So the walk is required to be a decision. A form reachable from a declaration that hands its
 * parts over is a form of the grammar, or one of the front end's settled answers, or it is erased
 * because a value cannot be read differently by it. There is no fourth, and this is what refuses
 * one.
 *
 * <p>Those and not the records. What the comparison walks with nobody having said so is what this
 * is about, and a record is how most of them are written rather than what makes one of them one: a
 * node written by hand is walked the same way, and something the comparison has an arm for is not
 * walked at all whatever it is written as. Asked of the records, a node written by hand joins the
 * comparison unanswered about.
 *
 * <p>Static, over what a declaration can reach rather than over what some fixture happened to build.
 * A form in a corner of the grammar no test writes would otherwise sit there until an author used
 * it, and be answered about then by nobody.
 */
class EveryFormADeclarationIsMadeOfIsClassifiedTest {

    /** What the comparison is handed: a declaration, a behavior's signature, a published helper.
     *  Everything it reaches, it reaches from one of these. */
    private static final List<Class<?>> ROOTS = List.of(
            Hir.Data.class, Hir.SumData.class, Hir.UnitData.class,
            Hir.SpecBehavior.class, Hir.PipeBehavior.class, Hir.FnDef.class);

    @Test
    void everyFormADeclarationReachesIsAFormOrASettledAnswerOrErased() {
        Set<Class<?>> reached = walkOfDeclarations().reached();

        assertFalse(reached.isEmpty(), "a walk that reaches nothing would pass for any reason");
        List<String> undecided = new ArrayList<>(new TreeSet<>(reached.stream()
                .filter(StructuralParts::areHandedOver)
                .filter(t -> !decided(t)).map(Class::getName).toList()));

        assertEquals(List.of(), undecided,
                "a declaration is made of these and the comparison has not decided about them."
                        + " Each is a form of the grammar, or one of the front end's settled"
                        + " answers, or erased because a value crossing between two builds cannot"
                        + " be read differently by it");
    }

    /**
     * The control: the walk can tell an undecided record from a decided one.
     *
     * <p>Without it, a walk that reached nothing but forms of the grammar — or one whose predicate
     * answered yes to everything — would pass while saying nothing.
     */
    @Test
    void andTheWalkWouldSeeAnUndecidedRecordIfThereWereOne() {
        assertFalse(decided(Undecided.class),
                "a record nothing here classifies is not passed over");
        assertFalse(DeclarationAgreement.isAFormOfTheGrammar(ValueName.Behavior.class),
                "a record the front end settled an answer as is not a form of the grammar");
        assertTrue(DeclarationAgreement.isASettledAnswer(ValueName.Behavior.class),
                "it is decided by being one of those, which is another way of deciding");
    }

    /**
     * What the comparison has an arm for is outside this, and says so itself.
     *
     * <p>A binding is the plainest one: the comparison holds two of them to standing for each other
     * across the two builds, so nothing of what one is made of is ever walked and there is no
     * account for this to want. Which is a fact about the comparison and is read off it — asked of
     * how a binding happens to be written, the day one is written as a record it would arrive here
     * demanding an account for an identity nobody compares.
     */
    @Test
    void whatTheComparisonHasAnArmForIsNotAskedForAnAccount() {
        assertFalse(StructuralParts.areHandedOver(BindingId.class),
                "the comparison does not walk a binding, so it is not one of these");
        assertFalse(DeclarationAgreement.comparedTheSameByItsOwnEquality(
                        new BindingId(new BindingOwner.OfValue("demo", "f"), 0)),
                "and what it does instead is the arm: this comparison answers about a binding what"
                        + " its own equality does not");
    }

    /**
     * A shape a node holds is a form of the grammar wherever it is written down.
     *
     * <p>Held here because the other way round is the one that says nothing: a form the tree is
     * made of, answered about by no account, is walked part by part all the same and every part it
     * reaches drops out of what anything has decided.
     */
    @Test
    void aShapeANodeHoldsIsAFormWhereverItIsWritten() {
        assertTrue(DeclarationAgreement.isAFormOfTheGrammar(WrittenName.class),
                "a name as written is held by node after node and is a form of the grammar for"
                        + " that, not for which file it is written in");
        assertFalse(DeclarationAgreement.isAFormOfTheGrammar(RowPosition.Supplies.class),
                "and what this compile numbered a row as is written in the same place and is not a"
                        + " form: the comparison erases it, which is where it is said");
        assertTrue(StructuralParts.areHandedOver(RowPosition.Supplies.class),
                "which is not the walk refusing to read it. Parts can be read off one, and the walk"
                        + " that looks for the declarations a crossing reaches reads them");
    }

    /**
     * A form of the grammar is one the tree holds, and the tree is not everything written beside it.
     *
     * <p>Where a type is written answers which of the tree's own shapes it is, and answers it for
     * everything else in the same package too. So what the sweep reaches from there is pinned: a
     * type joining this list is one somebody put in a declaration's reach, and what it is is a
     * decision — a form the tree holds, or a record this compile keeps about itself and erases.
     */
    @Test
    void theOnlyShapeTheTreeHoldsFromOutsideItsOwnFileIsAName() {
        List<String> beside = new ArrayList<>(new TreeSet<>(walkOfDeclarations().reached().stream()
                .filter(t -> t.getPackageName().equals(Hir.class.getPackageName()))
                .filter(t -> !t.getName().startsWith(Hir.class.getName() + "$"))
                .map(Class::getName).toList()));

        assertEquals(List.of(
                        // What a construct was made from, and what a definition was made as: both
                        // this compile's record of how it built its own tree, and both erased.
                        "souther.compiler.ast.ConstructionOrigin",
                        "souther.compiler.ast.DefinitionRole",
                        // And the one shape the tree holds that is written in its own file.
                        "souther.compiler.ast.WrittenName"),
                beside,
                "a declaration reaches these from where the tree is written, and each is answered"
                        + " about by where it is rather than by what it is");
    }

    /**
     * Two texts a rule was quoted from are one thing not compared.
     *
     * <p>The kind and not the arm, which is what a crossing needs it to be: one build reads a
     * module from the source it holds and another reads the text a published module was put back
     * together as, so one rule arrives with a different arm on each side as a matter of course.
     * Compared by which arm it is, every crossing of a rule written in a module read back would
     * report a build that has not moved.
     */
    @Test
    void whichTextARuleWasQuotedFromIsNotComparedByWhichKindOfTextItIs() {
        assertSame(DeclarationAgreement.erasedAs(QuotedFrom.ASourceThisCompileHolds.class),
                DeclarationAgreement.erasedAs(QuotedFrom.TextItCannotShow.class),
                "a source this compile holds and a text it cannot show are one erased thing");
        assertNotSame(DeclarationAgreement.erasedAs(QuotedFrom.TextItCannotName.class),
                DeclarationAgreement.erasedAs(SourcePos.class),
                "and two erased kinds stay two, so a text is not held against a position");
    }

    /**
     * The other control: a form the grammar has which is not a record hands its parts over, and this
     * walk goes through it.
     *
     * <p>Asked of the form's parts rather than of what the walk reached from a root. A type held
     * inside one is usually held somewhere else too, so a reachable set says the walk arrived and
     * not that it arrived this way — and the day a second route appears, a walk that stopped here
     * would go on passing. What this holds is that it does not stop.
     *
     * <p>A form written by hand rather than as a record is what the walk used to treat as a leaf,
     * and treating one as a leaf is the failure that says nothing: everything held inside it drops
     * out of what has been decided about, and the sweep above goes green over a smaller world.
     */
    @Test
    void aFormOfTheGrammarWrittenByHandHandsItsPartsOver() {
        assertTrue(StructuralParts.areHandedOver(Hir.RetType.class),
                "a written type is a form of the grammar however it is written");

        List<String> parts = new ArrayList<>();
        for (StructuralParts.Part part : StructuralParts.of(Hir.RetType.class)) {
            parts.add(part.name());
        }
        assertEquals(List.of("cases", "meaning", "pos"), parts,
                "the terms, what they come to, and where they are written: all three are held and"
                        + " all three are what this walk goes on to decide about");
    }

    /**
     * And this walk stops only where the comparison stops.
     *
     * <p>What it is for a walk to say something is that it arrives where the comparison arrives. A
     * type this stops at and the comparison goes inside is a part of a crossing that no account was
     * ever asked for: the comparison reads it, this test reaches nothing under it, and both go on
     * quietly. Which is not a wrong answer anywhere — it is a question nobody is asked.
     *
     * <p>The other direction is left open on purpose. The comparison stops early at a form it reads
     * by the answer, and this walk goes through such a form and into parts the comparison never
     * reads; reaching more than is read costs an account for something a crossing does not depend
     * on, and reaching less costs the account for something it does.
     */
    @Test
    void andTheWalkStopsOnlyWhereTheComparisonStops() {
        List<String> readInsideAllTheSame = new ArrayList<>(new TreeSet<>(
                walkOfDeclarations().stoppedAt().stream()
                        .filter(EveryFormADeclarationIsMadeOfIsClassifiedTest::comparisonGoesInside)
                        .map(Class::getName).toList()));

        assertEquals(List.of(), readInsideAllTheSame,
                "this walk stops at these and the comparison reads what is inside them, so what a"
                        + " crossing depends on there is decided by nobody and nothing says so");
    }

    /** Whether {@link DeclarationAgreement} holds two of them by walking their parts. */
    private static boolean comparisonGoesInside(Class<?> type) {
        return !DeclarationAgreement.erases(type) && StructuralParts.areHandedOver(type);
    }

    /** Stands for a record someone adds to a declaration without saying what it is. */
    private record Undecided(String what) {}

    /** Whether {@code type} is one the comparison has an answer for. */
    private static boolean decided(Class<?> type) {
        return DeclarationAgreement.isAFormOfTheGrammar(type)
                || DeclarationAgreement.isASettledAnswer(type)
                || DeclarationAgreement.erases(type);
    }

    /**
     * What the walk found: every type a published declaration reaches, and the ones it stopped at.
     *
     * @param reached   every type reachable from a declaration, the leaves among them
     * @param stoppedAt the ones whose parts this walk did not go on to
     */
    private record Walked(Set<Class<?>> reached, Set<Class<?>> stoppedAt) {}

    /**
     * Every type reachable from a published declaration, through record components and the
     * containers they are held in. A sealed type stands for its permitted forms.
     *
     * <p>Where it stops is read off the structure and off what the comparison passes over, and
     * never off how a type was classified. Those are two questions: whether something has been
     * decided about is one, and whether there is anything further in it to decide about is the
     * other, and one does not follow from the other. A walk steered by the classification stops
     * wherever an answer has been written down, so a form under one is reached by nobody and
     * decided by nobody, and this test goes on passing over a smaller world.
     */
    private static Walked walkOfDeclarations() {
        Set<Class<?>> seen = new LinkedHashSet<>();
        Deque<Class<?>> todo = new ArrayDeque<>(ROOTS);
        Set<Class<?>> reached = new LinkedHashSet<>();
        Set<Class<?>> stoppedAt = new LinkedHashSet<>();
        while (!todo.isEmpty()) {
            Class<?> type = todo.removeFirst();
            if (!seen.add(type) || type.isPrimitive()) {
                continue;
            }
            if (DeclarationAgreement.erases(type)) {
                reached.add(type);
                stoppedAt.add(type);
                continue;   // the comparison does not go inside one, so neither does this
            }
            if (type.isSealed()) {
                for (Class<?> permitted : type.getPermittedSubclasses()) {
                    todo.addLast(permitted);
                }
                continue;   // the interface itself holds nothing; its forms do
            }
            reached.add(type);
            if (type.isInterface() || !StructuralParts.areHandedOver(type)) {
                stoppedAt.add(type);
                continue;   // a leaf as far as this walk is concerned
            }
            for (StructuralParts.Part part : StructuralParts.of(type)) {
                for (Class<?> held : TypesAPartIsDeclaredToHold.named(part.held())) {
                    todo.addLast(held);
                }
            }
        }
        return new Walked(reached, stoppedAt);
    }
}
