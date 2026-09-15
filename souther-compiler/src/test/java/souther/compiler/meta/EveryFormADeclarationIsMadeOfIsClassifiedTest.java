package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.DefinitionName;
import souther.compiler.ast.Hir;
import souther.compiler.ast.RowPosition;
import souther.compiler.ast.WrittenName;
import souther.compiler.diag.QuotedFrom;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.ApplicationOrigin;
import souther.compiler.RecordOfTheBuilding;
import souther.compiler.SettledAnswer;
import souther.compiler.types.BindingId;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.RuleOrigin;
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
 * Every form a published declaration is made of says which of three things it is.
 *
 * <p>The comparison walks a form's components when it has nothing else to say about it, which is
 * right for a form of the grammar and is a default for everything else. A record the compiler puts
 * beside a declaration to say something about itself — which pass rewrote a node, what a coverage
 * point was numbered as — joins the comparison the day it is added, and two builds that mean the
 * same thing start disagreeing over it. Nothing says so: the language still compiles, every test
 * still passes, and what changed is what two builds are held to.
 *
 * <p>So the walk is required to be a decision. A form reachable from a declaration that hands its
 * parts over is one of three things: a form of the grammar, an answer the front end settled, or a
 * record this compile keeps about how it built what it built. There is no fourth, and this is what
 * refuses one.
 *
 * <p>Three things it is, and not three things done with it. Whether the comparison passes over a
 * form is the other question, answered where that reading is written, and it is no answer to this
 * one: a form says what it is whether or not anything looks at it. Most of them have both answers —
 * an application the author wrote is a record of the building and is also erased — and taking the
 * second for the first is how a form comes to be accounted for by what somebody does with it, which
 * is the same thing as being accounted for by what it is written next to.
 *
 * <p>Those and not the records. What the comparison walks with nobody having said so is what this
 * is about, and a record is how most of them are written rather than what makes one of them one: a
 * node written by hand is walked the same way, and something the comparison has an arm for is not
 * walked at all whatever it is written as. Asked of the records, a node written by hand joins the
 * comparison unanswered about.
 *
 * <p>Each of them is said by the type. A form of the grammar is one the tree holds or one that says
 * it is a shape; the other two are said by the types themselves in the package the front end writes
 * its answers in, which is also where this compile writes what it keeps about its own building. Read
 * off the package, a record added there would be handed an account nobody gave it, and the day
 * somebody wrote one that is neither, the comparison would take it up in silence.
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
    void everyFormADeclarationReachesSaysWhichOfTheThreeItIs() {
        Set<Class<?>> reached = walkOfDeclarations().reached();

        assertFalse(reached.isEmpty(), "a walk that reaches nothing would pass for any reason");
        List<String> answeredOtherThanOnce = new ArrayList<>(new TreeSet<>(reached.stream()
                .filter(StructuralParts::areHandedOver)
                .filter(type -> accountsGiven(type) != 1)
                .map(type -> type.getName() + " says " + accountsGiven(type) + " of them")
                .toList()));

        assertEquals(List.of(), answeredOtherThanOnce,
                "a declaration is made of these and each is to say which of three things it is: a"
                        + " form of the grammar, one of the front end's settled answers, or a record"
                        + " this compile keeps about reading a source and building what it built."
                        + " Saying none leaves the comparison walking into something nobody decided"
                        + " about, and saying two is two answers with nothing to say which governs."
                        + " Whether the comparison reads it is the other question and is no answer"
                        + " to this one");
    }

    /**
     * The control: the sweep can tell a form that says none of the three from one that says one,
     * and a form that says two from both.
     *
     * <p>Without the first, a walk that reached nothing but forms of the grammar — or one whose
     * predicate answered yes to everything — would pass while saying nothing. Without the second,
     * the sweep would be asking whether a form has been accounted for rather than what it is, and a
     * form carrying two accounts is what that difference is worth: it reads as decided, and which
     * of the two governs is what nobody said.
     */
    @Test
    void andTheSweepWouldSeeAFormThatSaysNoneOfThemOrTwo() {
        assertEquals(0, accountsGiven(Undecided.class),
                "a record nothing here classifies is not passed over");
        assertEquals(2, accountsGiven(Ambiguous.class),
                "and one written as both is not passed over either, which is what asking how many"
                        + " rather than whether is for");

        assertFalse(DeclarationAgreement.isAFormOfTheGrammar(ValueName.Behavior.class),
                "a record the front end settled an answer as is not a form of the grammar");
        assertEquals(1, accountsGiven(ValueName.Behavior.class),
                "it says one of them, which is the whole of what is asked");
    }

    /**
     * Each of the three is said by the type, and a record written beside them is told nothing.
     *
     * <p>The front end's answers and what this compile keeps about its own building are written in
     * one package, so where a file sits tells the two apart from nothing. Each says which it is, and
     * a record that says neither has been accounted for by nobody — which is what the sweep above
     * reports, and what it could not report while the package answered.
     */
    @Test
    void whichOfTheThreeAFormIsIsSaidByTheFormAndNotByWhereItIsWritten() {
        assertTrue(DeclarationAgreement.isASettledAnswer(ValueName.Behavior.class),
                "which declaration a name reaches is settled before a crossing sees either build");
        assertTrue(DeclarationAgreement.isARecordOfTheBuilding(ApplicationOrigin.Derived.class),
                "and an application a pass wrote, counted as it went, is what this compile kept"
                        + " about building it");
        assertFalse(DeclarationAgreement.isASettledAnswer(ApplicationOrigin.Derived.class),
                "a record of the building is not an answer about a declaration, and the package"
                        + " they share says neither");

        assertFalse(DeclarationAgreement.isASettledAnswer(ConstructOccurrence.class),
                "and a record written beside them that says neither is told neither by being"
                        + " written there");
        assertFalse(DeclarationAgreement.isARecordOfTheBuilding(ConstructOccurrence.class),
                "by either of them, whatever it is made of");
        assertEquals(0, accountsGiven(ConstructOccurrence.class),
                "so a declaration reaching one would be reaching a form nobody has said what it is,"
                        + " which is the finding this makes");
    }

    /**
     * The control for that: the forms under an erased sealed type are reached and asked.
     *
     * <p>Named rather than counted, because what this holds is that a whole corner of the world is
     * in sight. An erased sealed type stands for forms like any other, and a walk that stopped at
     * it would leave them reached by nobody — so the sweeps above would go green over the forms
     * that had never been put to them, and two sweeps written to catch different things would both
     * be blind in the same place.
     */
    @Test
    void andTheFormsUnderAnErasedSealedTypeAreAmongThemToo() {
        Set<Class<?>> reached = walkOfDeclarations().reached();

        assertTrue(reached.contains(QuotedFrom.ASourceThisCompileHolds.class),
                "a text a rule was quoted from is erased, and which texts there are is not that"
                        + " question and is not answered by it");
        assertTrue(DeclarationAgreement.erases(QuotedFrom.ASourceThisCompileHolds.class),
                "the comparison does pass over it, which is what makes it the one to ask about");
        assertEquals(1, accountsGiven(QuotedFrom.ASourceThisCompileHolds.class),
                "and being passed over is no reason to have said nothing about what it is");
    }

    /**
     * And what the comparison passes over is one erased thing, not the first of several.
     *
     * <p>The same question one door along. Which erased kind a form is decides what it is held
     * equal to — two erased forms match when they are the same kind — so a form answering to two of
     * them is a form whose answer is whichever was looked at first, and what is looked at first is
     * the iteration of a set, which is not written down anywhere and need not be the same twice.
     *
     * <p>Asked of what a declaration reaches, like the rest of this. A form that answered to two
     * would be compared one way in one run and another way in the next, and a comparison reporting
     * a build that has not moved is the thing this whole file exists to keep from happening
     * quietly.
     */
    @Test
    void andWhatIsPassedOverAnswersToOneErasedKind() {
        List<String> answeringToSeveral = new ArrayList<>(new TreeSet<>(
                walkOfDeclarations().reached().stream()
                        .filter(type -> erasedKindsOf(type).size() > 1)
                        .map(type -> type.getName() + " answers to " + erasedKindsOf(type))
                        .toList()));

        assertEquals(List.of(), answeringToSeveral,
                "these are held equal to whichever of their erased kinds was reached first, and"
                        + " nothing says which that is");
    }

    /** Every erased kind {@code type} answers to. */
    private static List<String> erasedKindsOf(Class<?> type) {
        List<String> kinds = new ArrayList<>();
        for (Class<?> erased : DeclarationAgreement.erasedKinds()) {
            if (erased.isAssignableFrom(type)) {
                kinds.add(erased.getSimpleName());
            }
        }
        return kinds;
    }

    /**
     * A copy of a body is a record of the building, and the place the copy was made at is not.
     *
     * <p>The two halves of it come apart, which is what makes it worth saying. A step is a call
     * written in a body, named in what the source settles and settled before either tree exists; a
     * lineage is the chain of them one reader walked, and the two representations of a body expand
     * different calls — so a construct inside a language operation has a chain in the tree where
     * that operation stands expanded and none in the tree where it stands. What the two trees agree
     * about is said elsewhere ({@link souther.compiler.types.ConstructOccurrence}), and it is not
     * this.
     *
     * <p>So the chain being built out of settled parts does not make the chain settled. Read the
     * other way, every materialisation naming itself in the source's own words would pass for
     * something the source said.
     */
    @Test
    void whichCopyOfABodyAConstructStandsInIsARecordOfTheBuilding() {
        assertTrue(DeclarationAgreement.isARecordOfTheBuilding(ExpansionLineage.Expansion.class),
                "a chain of copies is the one a reader walked, and another reading of the same"
                        + " source walks another");
        assertTrue(DeclarationAgreement.isASettledAnswer(ExpansionLineage.Step.class),
                "a step of it is a call the source wrote, which both readings meet the same");
        assertFalse(DeclarationAgreement.isASettledAnswer(ExpansionLineage.Expansion.class),
                "and being made of those does not make the chain one of them");
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
     * A shape the nodes hold is a form of the grammar because it says it is one.
     *
     * <p>The three answers a type written beside the tree can have, and each comes from something
     * that was decided rather than from where the file sits. A shape says it is syntax; a record
     * this compile keeps about its own building is erased, and that is said of it once; and a
     * record that is neither gets no account by being written next door.
     */
    @Test
    void aShapeIsAFormBecauseItSaysSoAndNotBecauseOfWhereItIsWritten() {
        assertTrue(DeclarationAgreement.isAFormOfTheGrammar(WrittenName.class),
                "a name as written is held by node after node and says it is syntax");
        assertFalse(DeclarationAgreement.isAFormOfTheGrammar(DefinitionName.class),
                "and what a definition is filed under is written beside the tree and says nothing,"
                        + " so it is a form of the grammar by nobody's decision");
        assertFalse(DeclarationAgreement.isAFormOfTheGrammar(RowPosition.Supplies.class),
                "nor is what this compile numbered a row as, which is written there too");
        assertTrue(StructuralParts.areHandedOver(RowPosition.Supplies.class),
                "which is not the walk refusing to read it. Parts can be read off one, and the walk"
                        + " that looks for the declarations a crossing reaches reads them");
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
     * Which rule a source wrote is one thing not compared, and it is that by a decision.
     *
     * <p>It is a record of the front end's, so the package rule answered for it and a crossing read
     * it on those terms. What it holds is an identity — which owner wrote the block, and which of
     * that owner's blocks it is — and the reader that needs one is the coverage that files what a
     * row exercised, not a crossing.
     *
     * <p>Its own kind, like every other erased thing. Held against a position or a text, a rule
     * would come back equal to them, and what is erased is a part a crossing cannot see rather than
     * a slot anything may turn up in.
     */
    @Test
    void whichBlockOfItsOwnerARuleIsIsNotWhatACrossingReadsItBy() {
        assertTrue(DeclarationAgreement.erases(RuleOrigin.class),
                "what a crossing depends on is what a rule admits, not the number its owner gave"
                        + " the block");
        assertNotSame(DeclarationAgreement.erasedAs(RuleOrigin.class),
                DeclarationAgreement.erasedAs(SourcePos.class),
                "and two erased kinds stay two, so a rule is not held against a position");
    }

    /**
     * Where an author put a call is not compared, and the other reasons an application is there
     * still are.
     *
     * <p>Erased one arm at a time, which is what the answers are. An application the author wrote
     * carries the construct it was written as, and that construct is answered where it is answered;
     * the arms beside it say a pass put the application there and name what it was following, which
     * is a question of its own and open.
     *
     * <p>So the arm and never what it is an arm of. Erased at the interface, a call the author wrote
     * and one a pass derived would be one thing not compared — two applications that are there for
     * different reasons, arriving as the same.
     */
    @Test
    void whereAnAuthorPutACallIsNotComparedAndTheOtherReasonsAreLeftOpen() {
        assertTrue(DeclarationAgreement.erases(ApplicationOrigin.Written.class),
                "what an application is is what it applies and what it is handed, and where it was"
                        + " written is not one of those");
        assertFalse(DeclarationAgreement.erases(ApplicationOrigin.Derived.class),
                "an application a pass wrote is there for a reason nobody has answered about yet,"
                        + " and it goes on being asked");
        assertNotSame(DeclarationAgreement.erasedAs(ApplicationOrigin.Written.class),
                DeclarationAgreement.erasedAs(RuleOrigin.class),
                "and two erased kinds stay two, so a call is not held against a rule");
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

    /** Stands for one that says it is two of them, which answers the question no better. */
    private record Ambiguous(String what) implements SettledAnswer, RecordOfTheBuilding {}

    /**
     * How many of the three {@code type} says it is.
     *
     * <p>Counted rather than asked whether any of them holds. What is wanted is which of the three
     * a form is, and a form saying two has not answered that — it has been given two answers with
     * nothing to say which governs, which is the shape this whole check is against.
     */
    private static int accountsGiven(Class<?> type) {
        int given = 0;
        if (DeclarationAgreement.isAFormOfTheGrammar(type)) {
            given++;
        }
        if (DeclarationAgreement.isASettledAnswer(type)) {
            given++;
        }
        if (DeclarationAgreement.isARecordOfTheBuilding(type)) {
            given++;
        }
        return given;
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
     *
     * <p><b>Which forms there are is settled before what is done with them is asked.</b> A sealed
     * type is not a form — its permitted ones are — so it stands for them whether or not the
     * comparison passes over it. Asked the other way round, an erased sealed type would stop the
     * walk at a name no value ever has, and the forms underneath it would be the ones nobody is
     * asked about: the same policy deciding what a form is, one step further back, where it
     * decides which forms there are to ask about at all.
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
            if (type.isSealed()) {
                for (Class<?> permitted : type.getPermittedSubclasses()) {
                    todo.addLast(permitted);
                }
                continue;   // the interface itself holds nothing; its forms do
            }
            if (DeclarationAgreement.erases(type)) {
                reached.add(type);
                stoppedAt.add(type);
                continue;   // the comparison does not go inside one, so neither does this
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
