package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.Instruction;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.instruction.FieldInstruction;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.constantpool.LoadableConstantEntry;
import java.lang.classfile.constantpool.MemberRefEntry;
import java.lang.classfile.constantpool.MethodHandleEntry;
import java.lang.constant.MethodTypeDesc;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every place this compiler starts a reading of a declaration that somebody else has already made
 * is written down here.
 *
 * <p>Reading a declaration is what a question about its rules costs, and the readings a question
 * needs beyond the first are readings of the same declaration again: attributing an end reads it
 * once per conjunct that could be holding one. So a reading is lent — made once for a declaration
 * under a revision and handed to whoever asks next — and where the lending is reached, a reader
 * says where it borrows from ({@code DeclarationReadings}).
 *
 * <p><b>A reader that says nothing gets nothing, and nothing about that fails.</b> An entry point
 * that took the rules and the budget apart could be offered beside one that also took the lending,
 * and the shorter would read for itself and answer the same. A caller that reached for it would
 * lose every reading the lending had to give and be told by nothing at all — which is how a
 * boundary search came to build a declaration's string machines again for each value it probed. So
 * a reader of a declaration's rules is handed a world, which always says where it borrows from, and
 * nothing in {@code check} or {@code inputs} takes the rules and the budget as two arguments but
 * what makes a world.
 *
 * <p><b>What is written down is the edge and not the place it arrives at.</b> A reader that starts
 * such a reading is reached by a call, and a table of readers says nothing about who is calling
 * them: a way in named here as allowed would let a new caller of it arrive with nothing to fail.
 * So each row is one production instruction reaching one place, both ends said in full, and the
 * whole set is compared — a row that has gone is as much a finding as one that has appeared.
 *
 * <p><b>Two claims and not one.</b> That this compiler can express an evaluation with no store
 * behind it, which is one way in and is named; and that nothing here spends one, which is no
 * readers at all. Read as a single population the second would be satisfied by the first going
 * missing, and a walk that had stopped reading call sites would report a compiler that starts no
 * such reading. So the way in is asserted to be there, and the readers to be none.
 *
 * <p>A test standing one declaration up to look at it is a reader with no store, and saying so is
 * not a defect: it asks for the world with nothing lent by name. What may not happen is this
 * compiler asking for one.
 *
 * <p>Read off the compiled classes, because what is being asked is which method a call site
 * resolved to and what a method takes, which are facts about resolution rather than about the
 * text: a walk over spellings would be deciding overload resolution again, and getting it wrong
 * quietly.
 *
 * <p><b>Every way an instruction names a method.</b> A call is one; handing the method over to be
 * called later is another, and that arrives as a handle among the arguments a bootstrap is given.
 * A reader that passes one of these along rather than calling it starts the same reading.
 */
class NothingHereStartsAReadingSomebodyElseHasAlreadyMadeTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String LENDING = "souther/compiler/check/DeclarationReadings";

    /** What a row names when a reader takes nothing to borrow from rather than reaching a way in
     *  that does. */
    private static final String NOTHING_TO_BORROW_FROM = LENDING + "#NONE";

    private static final String LENDING_TYPE = "L" + LENDING + ";";

    private static final String CHECK = "souther/compiler/check/";

    private static final String INPUTS = "souther/compiler/inputs/";

    private static final String THE_RULES = "L" + CHECK + "RuleReadingSource;";

    private static final String THE_BUDGET = "L" + CHECK + "ReadingPolicy;";

    private static final String SOURCE_AND_POLICY = THE_RULES + THE_BUDGET;

    /**
     * Every method of {@code check} and {@code inputs} that takes the rules and the budget as two
     * arguments, which is what makes a world and nothing else.
     *
     * <p>Named rather than counted, so that a walk that stopped reading what methods take comes
     * back with nothing and fails. A method added here is a way to read a declaration's rules
     * without saying where to borrow from; a method gone from here is a world nobody can make.
     * Each is named with what it takes ({@link AMethod}), so a shorter overload of one of them is
     * a row of its own.
     */
    private static final Set<String> TAKING_THE_RULES_AND_THE_BUDGET_APART = Set.of(
            AMethod.of(CHECK + "RuleReadingContext", "<init>",
                    "(" + SOURCE_AND_POLICY + LENDING_TYPE + ")V"),
            AMethod.of(CHECK + "RuleReadingContext", "of",
                    "(" + SOURCE_AND_POLICY + LENDING_TYPE + ")L" + CHECK + "RuleReadingContext;"),
            AMethod.of(CHECK + "RuleReadingContext", "unshared",
                    "(" + SOURCE_AND_POLICY + ")L" + CHECK + "RuleReadingContext;"));

    /**
     * The one way in that says outright it reads for itself, and the whole of what may say it.
     *
     * <p>An evaluation with no store behind it is a thing this compiler can express, and this is
     * how: a world made of rules and a budget and nothing lent, asked for by that name. A test
     * standing one declaration up to look at it is such an evaluation, and saying so is not a
     * defect — said by naming this rather than by assembling a world around
     * {@link #NOTHING_TO_BORROW_FROM}, so that why the lender is missing survives being read back.
     *
     * <p>Which is why the row is here rather than gone. What was settled is that no walk over what
     * an author wrote reads for itself, not that a reading with nowhere to borrow from stopped
     * being a thing anybody may build. A second way in is a finding; so is this one's
     * disappearance, and that is what makes it the control below.
     */
    private static final String THE_WAY_IN_THAT_READS_FOR_ITSELF =
            CHECK + "RuleReadingContext#unshared(" + SOURCE_AND_POLICY + ")L" + CHECK
                    + "RuleReadingContext; -> " + NOTHING_TO_BORROW_FROM;

    /**
     * Every reader of this compiler that reaches one, which is none of them.
     *
     * <p>Apart from the way in above because they are two claims. That one is about what this
     * compiler can express; this one is about who spends it — and a walk over what an author wrote
     * spends it nowhere, because the world it is handed says where to borrow from and is handed on
     * as it arrived ({@code RuleReadingContext}).
     *
     * <p>Empty, and an entry is a finding. A reader here is one that was given a world and read
     * past it: what it makes is filed under a source nothing lends against, and the reading
     * somebody already made of that declaration is paid for a second time.
     */
    private static final Set<String> EDGES_INTO_A_READING_OF_ONES_OWN = Set.of();

    /**
     * Only a world is made of the rules and the budget.
     *
     * <p>What keeps a reader from being offered a way in that leaves the lending out. A method
     * taking the rules and the budget apart takes them without the lending unless it takes that as
     * well, and one that takes all three is a world taken apart — which a step under a walk then
     * hands on as three, and the next step down is free to put together with some other lender.
     */
    @Test
    void onlyAWorldIsMadeOfTheRulesAndTheBudget() {
        Set<String> found = new TreeSet<>();
        for (ClassModel read : COMPILED.all()) {
            String owner = read.thisClass().name().stringValue();
            if (!owner.startsWith(CHECK) && !owner.startsWith(INPUTS)) {
                continue;
            }
            for (MethodModel method : read.methods()) {
                StringBuilder taken = new StringBuilder();
                method.methodTypeSymbol().parameterList()
                        .forEach(each -> taken.append(each.descriptorString()));
                if (taken.indexOf(THE_RULES) >= 0 && taken.indexOf(THE_BUDGET) >= 0) {
                    found.add(AMethod.of(read, method));
                }
            }
        }
        assertEquals(new TreeSet<>(TAKING_THE_RULES_AND_THE_BUDGET_APART), found,
                "what takes the rules and the budget as two arguments is not what makes a world;"
                        + " take the world instead");
    }

    /**
     * The way in that reads for itself is the one written down, and it is there.
     *
     * <p>The population's other half: a second way in is a reading with nowhere to borrow from that
     * nobody wrote down as one, and this one's disappearance is a way in that stopped saying what
     * it is.
     *
     * <p>Not the control for the emptiness below. This row is named by a {@code GETSTATIC}, so what
     * it witnesses is that one of the three ways an instruction names a member is read. The
     * emptiness is about the other two.
     */
    @Test
    void theWayInThatReadsForItselfIsFound() {
        assertEquals(Set.of(THE_WAY_IN_THAT_READS_FOR_ITSELF), waysInReachingNothingToBorrowFrom(),
                "the ways in that read for themselves are not the one written down");
    }

    /**
     * Each way an instruction names a member is read, witnessed on a member known to be named that
     * way.
     *
     * <p>The control for the emptiness below, and it takes three because {@link #whatItNames} has
     * three answers and they are three extractions. A member called is one; a static field read is
     * another; a member handed over to be called later is a third, and it is named among the
     * arguments a bootstrap is given rather than by an instruction of its own. Blinding any one of
     * them leaves the other two reading, so a control standing on one says nothing about the rest.
     *
     * <p>What that costs is the claim below. A reader reaching a reading of its own reaches it by
     * calling, so the emptiness there is an answer about the first of the three — and blinding that
     * one empties it, which is what a compiler with no such reader looks like. Witnessed here
     * instead, on members this test does not otherwise depend on.
     *
     * <p>Three assertions and not a walk over the three: nothing here can ask a switch what cases
     * it has. A fourth way to name a member is a fourth line, and is noticed where the case is
     * written rather than by anything failing.
     */
    @Test
    void everyWayAnInstructionNamesAMemberIsRead() {
        assertTrue(whatIsNamedIn(CHECK + "RuleReadingContext", "whileTheAnswerIsMade")
                        .contains(LENDING + "#whileTheAnswerIsMade"),
                "a member that is called is not read: deriving a bounded world calls the lender's"
                        + " own, and nothing here saw it");
        assertTrue(whatIsNamedIn(CHECK + "RuleReadingContext", "unshared")
                        .contains(NOTHING_TO_BORROW_FROM),
                "a static field that is read is not read: the way in names what there is nothing to"
                        + " borrow from, and nothing here saw it");
        assertTrue(whatIsNamedIn(CHECK + "InvariantChecker", "capabilityOf")
                        .contains(CHECK + "Terms#placeSubject"),
                "a member handed over to be called later is not read: reading a clause on its own"
                        + " hands over where a name stands, and nothing here saw it");
    }

    /** Every member named by any instruction of any method called {@code method} on {@code owner},
     *  read the way the walk below reads one. */
    private static Set<String> whatIsNamedIn(String owner, String method) {
        Set<String> named = new TreeSet<>();
        for (ClassModel read : COMPILED.all()) {
            if (!read.thisClass().name().stringValue().equals(owner)) {
                continue;
            }
            for (MethodModel each : read.methods()) {
                if (!each.methodName().stringValue().equals(method)) {
                    continue;
                }
                for (Instruction instruction : instructionsOf(each)) {
                    for (Named what : whatItNames(instruction)) {
                        named.add(what.member());
                    }
                }
            }
        }
        return named;
    }

    /**
     * No reader of this compiler reaches a reading nobody else made.
     *
     * <p>Compared whole and in both directions. An edge nobody wrote down is a reader that lost its
     * lending with nothing to say so; a row nothing reaches any more is a licence outliving what it
     * was for.
     */
    @Test
    void nothingHereReachesAReadingOfItsOwn() {
        Set<String> reaching = readersReachingAReadingOfTheirOwn();
        assertEquals(EDGES_INTO_A_READING_OF_ONES_OWN, reaching,
                () -> "the edges into a reading nobody else made are not the ones written down.\n"
                        + "  found and not written down:\n    "
                        + String.join("\n    ", minus(reaching, EDGES_INTO_A_READING_OF_ONES_OWN))
                        + "\n  written down and not found:\n    "
                        + String.join("\n    ", minus(EDGES_INTO_A_READING_OF_ONES_OWN, reaching))
                        + "\nHand this reader the world its caller read in, rather than a world"
                        + " with nothing lent to it.");
    }

    /**
     * Every edge into a reading nobody else made, said in full at both ends.
     *
     * <p>Walked once for the class. The two questions below are two readings of one walk over every
     * method of every compiled class, and asking each of them for its own walk reads the whole
     * output twice to answer about the same instructions.
     */
    private static Set<String> everyEdgeIntoAReadingOfOnesOwn() {
        if (EVERY_EDGE == null) {
            EVERY_EDGE = walkForEveryEdgeIntoAReadingOfOnesOwn();
        }
        return EVERY_EDGE;
    }

    private static Set<String> EVERY_EDGE;

    private static Set<String> walkForEveryEdgeIntoAReadingOfOnesOwn() {
        Set<Named> waysIn = theWaysInThatSayTheyReadForThemselves();
        Set<String> reaching = new TreeSet<>();
        for (ClassModel read : COMPILED.all()) {
            for (MethodModel method : read.methods()) {
                String from = AMethod.of(read, method);
                for (Instruction instruction : instructionsOf(method)) {
                    for (Named named : whatItNames(instruction)) {
                        if (startsAReadingOfItsOwn(waysIn, named)) {
                            reaching.add(from + " -> " + named.member());
                        }
                    }
                }
            }
        }
        return reaching;
    }

    /** Those of them whose reader is a way in saying it reads for itself, which is how one of those
     *  is written rather than a place this compiler spends one. */
    private static Set<String> waysInReachingNothingToBorrowFrom() {
        Set<String> found = new TreeSet<>();
        for (String edge : everyEdgeIntoAReadingOfOnesOwn()) {
            if (edge.endsWith(" -> " + NOTHING_TO_BORROW_FROM)) {
                found.add(edge);
            }
        }
        return found;
    }

    /** And those whose reader is anything else, which is this compiler spending one. */
    private static Set<String> readersReachingAReadingOfTheirOwn() {
        Set<String> found = new TreeSet<>();
        for (String edge : everyEdgeIntoAReadingOfOnesOwn()) {
            if (!edge.endsWith(" -> " + NOTHING_TO_BORROW_FROM)) {
                found.add(edge);
            }
        }
        return found;
    }

    private static List<String> minus(Set<String> these, Set<String> those) {
        return these.stream().filter(each -> !those.contains(each)).sorted().toList();
    }

    /**
     * What an instruction names: nothing, a member it calls, or a member it hands over to be called
     * later.
     *
     * <p>The last is what a method reference comes to. A reader passing one along starts the
     * reading the same way a caller does, and it is named in the arguments a bootstrap is given
     * rather than in an instruction of its own.
     */
    private static List<Named> whatItNames(Instruction instruction) {
        return switch (instruction) {
            case InvokeInstruction call -> List.of(new Named(
                    call.owner().name().stringValue() + "#" + call.name().stringValue(),
                    call.typeSymbol()));
            case FieldInstruction field when field.opcode() == Opcode.GETSTATIC -> List.of(
                    new Named(field.owner().name().stringValue() + "#"
                            + field.name().stringValue(), null));
            case InvokeDynamicInstruction handed -> {
                List<Named> named = new ArrayList<>();
                for (LoadableConstantEntry each
                        : handed.invokedynamic().bootstrap().arguments()) {
                    if (each instanceof MethodHandleEntry handle) {
                        MemberRefEntry member = handle.reference();
                        // A handle onto a field names a field, whose descriptor is not a method's.
                        // What it reaches is the member, and a member with nothing to take is not
                        // one of the entry points this is about.
                        String type = member.type().stringValue();
                        named.add(new Named(member.owner().name().stringValue() + "#"
                                + member.name().stringValue(),
                                type.startsWith("(") ? MethodTypeDesc.ofDescriptor(type) : null));
                    }
                }
                yield named;
            }
            default -> List.of();
        };
    }

    /** A member an instruction names: which one, and what it takes where that is a method. */
    private record Named(String member, MethodTypeDesc taking) {}

    /**
     * Whether reaching {@code named} is starting a reading nobody else made.
     *
     * <p>Which method, and not which name: a way in is found with what it takes, so an overload of
     * the same name that takes something to borrow from is not one.
     */
    private static boolean startsAReadingOfItsOwn(Set<Named> waysIn, Named named) {
        return named.member().equals(NOTHING_TO_BORROW_FROM) || waysIn.contains(named);
    }

    /**
     * The ways in that say outright that they read for themselves.
     *
     * <p>Derived and not listed: a method that takes nothing to borrow from is one that names the
     * lending there is nothing to borrow from. So a way in written later is one the day it is
     * written, and one whose reason is settled leaves the population when the naming goes.
     */
    private static Set<Named> theWaysInThatSayTheyReadForThemselves() {
        Set<Named> found = new LinkedHashSet<>();
        for (ClassModel read : COMPILED.all()) {
            String owner = read.thisClass().name().stringValue();
            for (MethodModel method : read.methods()) {
                for (Instruction instruction : instructionsOf(method)) {
                    for (Named named : whatItNames(instruction)) {
                        if (named.member().equals(NOTHING_TO_BORROW_FROM)) {
                            found.add(new Named(owner + "#" + method.methodName().stringValue(),
                                    method.methodTypeSymbol()));
                        }
                    }
                }
            }
        }
        return found;
    }

    /** Whether anything at all was read, so that an empty population fails rather than passes. */
    @Test
    void theCompiledClassesWereRead() {
        assertFalse(COMPILED.all().isEmpty(), "this repository compiled nothing to read");
    }

    private static List<Instruction> instructionsOf(MethodModel method) {
        Optional<java.lang.classfile.CodeModel> code = method.code();
        return code.map(each -> each.elementList().stream()
                .filter(Instruction.class::isInstance)
                .map(Instruction.class::cast)
                .toList()).orElse(List.of());
    }
}
