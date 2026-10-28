package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * An element compared against a value beside the list is reached at every value of both, though
 * the comparison sits in one case of the element and the list is held to more than one element.
 *
 * <p>That the arm is the one the element is says what stands there and nothing of how many
 * elements there are but that there is one, so a list holding an element of that case is a run
 * that gets to the comparison. A rule that reads only how many a list holds says nothing of what
 * its elements are, whether it asks for one or for two, so it leaves each element every value.
 * A rule keeping the elements apart is a reading of its own, and the control below holds that it
 * is still asked.
 */
class ARelationReachedOnlyInOneCaseOfAnElementIsReachedAtEveryValueTest {

    private static final String DECLARED = """
            module example.cases

            data UserId = String
                invariant String.length(value) >= 1

            data Call = { owner: UserId }
            data Meeting = { owner: UserId, minutes: Int }
            data Activity = Call | Meeting

            data Several = List<Meeting>
                invariant atLeastTwo = List.length(value) >= 2

            data Apart = List<Meeting>
                invariant atLeastTwo = List.length(value) >= 2
                invariant different = List.allDistinctBy(.owner, value)

            let meetingOf (a: Activity, owner: UserId): List<Meeting> =
                match a with
                    | Call -> []
                    | Meeting as m -> if m.owner == owner then [ m ] else []

            behavior inACase : (activities: List<Activity>, owner: UserId) -> List<Meeting>

            let inACase (activities, owner) = List.flatMap(a -> meetingOf(a, owner), activities)

            behavior ofSeveral : (meetings: Several, owner: UserId) -> List<Meeting>

            let ofSeveral (meetings, owner) = List.filter(m -> m.owner == owner, meetings.value)

            behavior keptApart : (meetings: Apart, owner: UserId) -> List<Meeting>

            let keptApart (meetings, owner) = List.filter(m -> m.owner == owner, meetings.value)

            data ByMail = { email: String }
            data ByPhone = { phone: String }
            data Reach = ByMail | ByPhone
            data Contact = { id: String, reach: Reach }

            data FreeBook = List<Contact>

            data Book = List<Contact>
                invariant different = List.allDistinctBy(.id, value)

            let mailOf (r: Reach): List<String> =
                match r with
                    | ByMail { email } -> [ email ]
                    | ByPhone { phone } -> []

            let isMailedTo (mail: String, r: Reach): Bool =
                match r with
                    | ByMail { email = own } -> own == mail
                    | ByPhone { phone } -> false

            data NotApart = List<Contact>
                invariant List.allDistinctBy(.id, value) == false

            data ApartOrMany = List<Contact>
                invariant List.allDistinctBy(.id, value) || List.length(value) >= 3

            data ApartAndTwo = List<Contact>
                invariant List.allDistinctBy(.id, value) && List.length(value) >= 2

            data ApartAndFew = List<Contact>
                invariant List.allDistinctBy(.id, value) && List.length(value) <= 5

            behavior throughNotApart : (reach: Reach, contacts: NotApart) -> List<Contact>

            let throughNotApart (reach, NotApart(rows)) =
                List.flatMap(mail -> List.filter(c -> isMailedTo(mail, c.reach), rows),
                        mailOf(reach))

            behavior throughApartOrMany : (reach: Reach, contacts: ApartOrMany) -> List<Contact>

            let throughApartOrMany (reach, ApartOrMany(rows)) =
                List.flatMap(mail -> List.filter(c -> isMailedTo(mail, c.reach), rows),
                        mailOf(reach))

            behavior throughApartAndTwo : (reach: Reach, contacts: ApartAndTwo) -> List<Contact>

            let throughApartAndTwo (reach, ApartAndTwo(rows)) =
                List.flatMap(mail -> List.filter(c -> isMailedTo(mail, c.reach), rows),
                        mailOf(reach))

            behavior throughApartAndFew : (reach: Reach, contacts: ApartAndFew) -> List<Contact>

            let throughApartAndFew (reach, ApartAndFew(rows)) =
                List.flatMap(mail -> List.filter(c -> isMailedTo(mail, c.reach), rows),
                        mailOf(reach))

            behavior throughFree : (reach: Reach, contacts: FreeBook) -> List<Contact>

            let throughFree (reach, FreeBook(rows)) =
                List.flatMap(mail -> List.filter(c -> isMailedTo(mail, c.reach), rows),
                        mailOf(reach))

            behavior throughBook : (reach: Reach, contacts: Book) -> List<Contact>

            let throughBook (reach, Book(rows)) =
                List.flatMap(mail -> List.filter(c -> isMailedTo(mail, c.reach), rows),
                        mailOf(reach))
            """;

    /** Said at each of the two places the comparison reads. */
    private static final List<BlockReason.RuleWithoutLineReason> RELATES_TWO_VALUES = List.of(
            new BlockReason.ComparisonRelatingTwoValues(),
            new BlockReason.ComparisonRelatingTwoValues());

    @Test
    void aComparisonInOneCaseOfTheElementRelatesTwoValues() {
        assertEquals(RELATES_TWO_VALUES, whyNoLine("inACase"),
                "a run that reaches it is a list of one element of that case");
    }

    @Test
    void aListHeldToTwoElementsLeavesEachElementEveryValue() {
        assertEquals(RELATES_TWO_VALUES, whyNoLine("ofSeveral"),
                "two elements may be one value, and the count says no more of them");
    }

    @Test
    void aRuleKeepingTheElementsApartIsStillAskedOfThem() {
        assertEquals(List.of(), whyNoLine("keptApart"),
                "the owners differ, so an owner is not every value of an element, and the"
                        + " comparison is not said to relate two values");
    }

    @Test
    void aListOfOneElementIsApartFromNothingSoTheRuleKeepingElementsApartDoesNotStopTheRun() {
        assertEquals(List.of(), notReachedAtEveryValue("throughFree"),
                "the control: the elements are held by nothing");
        assertEquals(List.of(), notReachedAtEveryValue("throughBook"),
                "a run that reaches the comparison holds one element, which no rule keeping"
                        + " elements apart refuses");
    }

    /**
     * A list of one element meets a rule that keeps elements apart, and no other rule that has the
     * call in it: a rule saying they are not apart, or apart or many, or apart and at least two,
     * is met by no list of one, or by one only because of what else it says. The run is then not
     * shown to get to the comparison for the mails it reads.
     */
    @Test
    void aRuleThatReadsTheCallButDoesNotNeedItTrueLeavesTheRunNotShownToGetThere() {
        List<String> stopped = List.of("contacts[*].reach@ByMail.email", "reach@ByMail.email");
        assertEquals(stopped, notReachedAtEveryValue("throughNotApart"),
                "the elements are held not to be apart, which a list of one is");
        assertEquals(stopped, notReachedAtEveryValue("throughApartOrMany"),
                "the call is one way to meet the rule and not the only one");
        assertEquals(stopped, notReachedAtEveryValue("throughApartAndTwo"),
                "a list of one holds fewer than the rule asks");
        assertEquals(List.of(), notReachedAtEveryValue("throughApartAndFew"),
                "the call is needed and the rest of the rule is met by a list of one");
    }

    /**
     * The domains of the mails of a lead, found before the contacts on those mails are: each mail
     * hands an attempt at a domain name, which a refused attempt leaves out. {@code contactsOnTheMail}
     * reads the contacts on a mail alone, and the reading reports the stop of {@code screen} only
     * with it beside.
     */
    private static final String AFTER_AN_ATTEMPT = """
            module example.screening exposing (
                EmailAddress, DomainName, EmailOnly, PhoneOnly, EmailAndPhone, Reach, Contact,
                Contacts, ContactId, Account, Book, Found, NoMail, NothingFound,
                contactsOnTheMail, screen
            )

            data EmailAddress = String
                invariant String.matches("[^@\\\\s]+@[^@\\\\s]+\\\\.[^@\\\\s]+", value)
            data DomainName = String
                invariant String.matches("[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?(\\\\.[a-z0-9]([a-z0-9\\\\-]*[a-z0-9])?)+", value)
            data ContactId = String   invariant String.length(value) >= 1

            data EmailOnly = { email: EmailAddress }
            data PhoneOnly = { phone: String }
            data EmailAndPhone = { email: EmailAddress, phone: String }
            data Reach = EmailOnly | PhoneOnly | EmailAndPhone
            data Contact = { id: ContactId, reach: Reach }
            data Contacts = List<Contact>
                invariant List.allDistinctBy(.id, value)
            data Account = { id: ContactId, domain: DomainName? }
            data Book = List<Account>
                invariant List.allDistinctBy(.id, value)

            let emailOf (reach: Reach): List<EmailAddress> =
                match reach with
                    | EmailOnly { email } -> [ email ]
                    | EmailAndPhone { email } -> [ email ]
                    | PhoneOnly { phone } -> []

            let reachHasEmail (email: EmailAddress, reach: Reach): Bool =
                match reach with
                    | EmailOnly { email = own } -> own == email
                    | EmailAndPhone { email = own } -> own == email
                    | PhoneOnly { phone } -> false

            let contactsOnEmail (email: EmailAddress, Contacts(rows)): List<Contact> =
                List.filter(c -> reachHasEmail(email, c.reach), rows)

            let emailMatches (reach: Reach, contacts: Contacts): List<Contact> =
                List.flatMap(e -> contactsOnEmail(e, contacts), emailOf(reach))

            let domainOf (email: EmailAddress): List<DomainName> =
                match List.get(1, String.split("@", email.value)) with
                    | Some d -> if DomainName(d) as name then [ name ] else []
                    | None -> []

            let hasDomain (domain: DomainName, a: Account): Bool =
                match a.domain with
                    | Some own -> own == domain
                    | None -> false

            let accountsOnDomain (domain: DomainName, Book(rows)): List<Account> =
                List.filter(a -> hasDomain(domain, a), rows)

            let domainMatches (reach: Reach, accounts: Book): List<Account> =
                List.flatMap(d -> accountsOnDomain(d, accounts), List.flatMap(e -> domainOf(e), emailOf(reach)))

            data Found = { accounts: List<ContactId>, contacts: List<ContactId> }  invariant List.length(accounts) + List.length(contacts) >= 1
            data NoMail
            data NothingFound

            behavior screen : (reach: Reach, accounts: Book, contacts: Contacts) -> NothingFound | Found | NoMail
                constructs Found, DomainName
            let screen (reach, accounts, contacts) = {
                guard List.length(emailOf(reach)) >= 1 else NoMail
                let ma = List.map(a -> a.id, domainMatches(reach, accounts))
                let mc = List.map(c -> c.id, emailMatches(reach, contacts))
                guard List.length(ma) + List.length(mc) >= 1 else NothingFound
                Found { accounts = ma, contacts = mc }
            }

            behavior contactsOnTheMail : (reach: Reach, contacts: Contacts) -> List<Contact>
            let contactsOnTheMail (reach, contacts) = emailMatches(reach, contacts)
            """;

    @Test
    void anAttemptedConstructionBeforeARelationStopsNoRunOnTheMailsItReads() {
        assertEquals(List.of(), notReachedAtEveryValue(AFTER_AN_ATTEMPT, "screen"),
                "an attempt refused takes the other arm and holds at most one element");
    }

    /** The places a relation is read at that the run is not shown to get to at every value. */
    private static List<String> notReachedAtEveryValue(String behavior) {
        return notReachedAtEveryValue(DECLARED, behavior);
    }

    private static List<String> notReachedAtEveryValue(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        PartitionEvidence evidence = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value().get(behavior);
        assertNotNull(evidence, "the model under test compiles");
        return evidence.notRead().stream()
                .filter(each -> each.reason()
                        == UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE)
                .map(PartitionEvidence.NotRead::at).sorted().distinct().toList();
    }

    /** The reasons for which a rule of {@code behavior} came to no line, one for each place. */
    private static List<BlockReason.RuleWithoutLineReason> whyNoLine(String behavior) {
        Compilation compilation = Compilation.ofSource(DECLARED, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        PartitionEvidence evidence = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value().get(behavior);
        assertNotNull(evidence, "the model under test compiles");
        return evidence.rulesWithoutALine().stream().map(RuleWithoutALine::why).toList();
    }
}
