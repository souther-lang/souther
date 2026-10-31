package souther.compiler.partition;

import java.util.Map;

import static souther.compiler.partition.ReadingRole.ACCRUES;
import static souther.compiler.partition.ReadingRole.ASKED;
import static souther.compiler.partition.ReadingRole.BUDGET;
import static souther.compiler.partition.ReadingRole.CACHE;
import static souther.compiler.partition.ReadingRole.COUNTER;
import static souther.compiler.partition.ReadingRole.FIXED;
import static souther.compiler.partition.ReadingRole.FLAG;
import static souther.compiler.partition.ReadingRole.FOOTPRINT;
import static souther.compiler.partition.ReadingRole.GUARDED;
import static souther.compiler.partition.ReadingRole.INPUT;
import static souther.compiler.partition.ReadingRole.LEDGER;
import static souther.compiler.partition.ReadingRole.MEMO;
import static souther.compiler.partition.ReadingRole.TRIAL;
import static souther.compiler.partition.ReadingRole.WRITTEN;

/**
 * The role each field of a {@link Pullback} has in a reading kept to be taken again.
 *
 * <p>Read off how the field is used: a field that a reading sets for the extent of a part and puts
 * back is an input, because what the part comes to turns on it; one a reading adds to and takes
 * back out of, or empties, is guarded, because taking the reading again would not do that; one
 * that is only added to and never asked after is not in the way.
 */
final class ReadingRoles {

    static final Map<String, ReadingRole> OF_A_PULLBACK = Map.ofEntries(
            Map.entry("read", FIXED),
            Map.entry("where", FIXED),
            Map.entry("subjects", FIXED),
            // The parts a reading met, which a rule set aside takes back out.
            Map.entry("met", LEDGER),
            // Answers worked out once for each step or arm, whoever asked first.
            Map.entry("trying", CACHE),
            Map.entry("entered", CACHE),
            // Set for the extent of a part and put back.
            Map.entry("quantifying", INPUT),
            Map.entry("parting", INPUT),
            Map.entry("askedAt", INPUT),
            Map.entry("restatingAQuotient", INPUT),
            Map.entry("beforeTheFork", INPUT),
            Map.entry("inTheListsOfAFlattening", INPUT),
            Map.entry("sideAsWritten", INPUT),
            Map.entry("sizedInACase", INPUT),
            Map.entry("carried", INPUT),
            Map.entry("recursed", INPUT),
            Map.entry("recursing", INPUT),
            Map.entry("sizedBelow", INPUT),
            Map.entry("sizedSoFar", INPUT),
            Map.entry("carriedSoFar", INPUT),
            Map.entry("onTheWay", INPUT),
            Map.entry("askingWhereAStepAnswers", INPUT),
            Map.entry("truthsDecided", INPUT),
            // Which part answers for a quantity is asked after by the reading of a count.
            Map.entry("armsTaken", INPUT),
            // Added to by a reading and taken back from, and asked what is in.
            Map.entry("counting", GUARDED),
            Map.entry("operated", GUARDED),
            // Added to by a reading where there is one, and never asked what is in: whoever set
            // it up reads it after.
            Map.entry("alike", WRITTEN),
            Map.entry("answering", WRITTEN),
            Map.entry("countsMet", WRITTEN),
            // Whether an aggregate is being read in every way it is kept, and not what it holds:
            // a reading that reads another aggregate is not kept.
            Map.entry("keptReading", FLAG),
            Map.entry("aggregatesInACase", ASKED),
            // Added to and not asked after by any reading.
            Map.entry("readOff", ACCRUES),
            Map.entry("triedAndConcluded", ACCRUES),
            Map.entry("underTrial", TRIAL),
            Map.entry("elementsMet", FOOTPRINT),
            Map.entry("readingsLeft", BUDGET),
            Map.entry("keptReadings", COUNTER),
            Map.entry("aggregatesKept", COUNTER),
            Map.entry("aggregatesAsked", COUNTER),
            Map.entry("sharedSums", MEMO),
            Map.entry("sharedApplications", MEMO),
            Map.entry("sharedConditions", MEMO));

    private ReadingRoles() {}
}
