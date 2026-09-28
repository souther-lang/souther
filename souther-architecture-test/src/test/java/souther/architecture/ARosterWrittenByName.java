package souther.architecture;

import java.lang.constant.ClassDesc;
import java.lang.constant.MethodTypeDesc;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

/**
 * A roster of members written by name, and what holds a name to being one member.
 *
 * <p>A rule that writes down which members do something has to say which member each row is. Said
 * as a whole signature, a row moves whenever the member's signature does — a parameter added, a
 * {@code Map} that became a {@code SequencedMap}, a return type replaced — and the rule is edited
 * for a change that left what it claims untouched. Said as a name, a row is as still as the design
 * it is about, and what it costs is that a name can hold several members.
 *
 * <p>So a name is spelt where a name is one member, and the overloads are spelt apart where they
 * are not. Which of those a name is is not the author's to judge: every overload the population
 * declares is looked up, and a name whose overloads the walk answered alike is one member as far as
 * the rule is concerned. A name whose overloads were answered differently is several, and a row
 * saying only the name would be saying one of the answers about all of them.
 *
 * <p><b>That is what a signature was bought for, and it is kept.</b> An overload added later that
 * the walk answers differently makes its name disagree, and a roster with nothing said about which
 * overload it means is refused rather than quietly covering the new one. What a row spells in that
 * case is the least that tells the overloads apart — which parameter, and what it is — and a
 * parameter added beside it still moves nothing.
 *
 * @param declared every member of the population, as owner, name and descriptor
 * @param told     which overload a row means, for each name whose overloads are not answered alike
 */
record ARosterWrittenByName(Set<String> declared, List<Told> told) {

    /**
     * Which overload of a name a row is about, said as the one parameter that tells it from its
     * siblings.
     *
     * <p>The parameter and not the signature, because a signature says the whole of what the member
     * takes and a row only has to say which of the overloads it is. A parameter added beside the
     * one that tells them apart moves nothing here.
     *
     * <p>Written as a class where this module can name one, so that a type renamed is a compile
     * error rather than a rule that goes on looking for a name nothing has. A type the module
     * cannot name — one its own package keeps to itself — is spelt, and a rename of that one is an
     * edit here.
     *
     * @param owner     the class that declares it, as a class file names it
     * @param name      the member, which several of its overloads share
     * @param at        which parameter tells this overload from the others of the name
     * @param parameter what that parameter is
     */
    record Told(String owner, String name, int at, ClassDesc parameter) {

        /** Told apart by a parameter of a type this module can name. */
        static Told takingA(String owner, String name, int at, Class<?> parameter) {
            return new Told(owner, name, at, parameter.describeConstable().orElseThrow());
        }

        /** And by one it cannot, which is a type its own package keeps to itself.
         *
         *  @param parameter as a class file names the type, with {@code /} between the steps */
        static Told takingWhatIsCalled(String owner, String name, int at, String parameter) {
            return new Told(owner, name, at, ClassDesc.ofInternalName(parameter));
        }

        /**
         * The member, as a row that has to tell two overloads apart is written.
         *
         * <p>The type as a class file names it, and not the last step of it. This is the key the
         * roster is written under and read back by, so two rows that pick different members have
         * to be two spellings: shortened to what the type is called, a row for
         * {@code a/Subject} and one for {@code b/Subject} are one string, and the member written
         * under it is whichever of them the walk answered last.
         */
        String spelt() {
            return owner + "#" + name + "[" + at + "=" + asAClassFileNamesIt(parameter) + "]";
        }

        /** Whether this is what {@code member} is called. */
        private boolean names(String member) {
            return (owner + "#" + name).equals(member);
        }

        /** Whether the overload {@code descriptor} spells is the one this picks out. */
        boolean picks(String descriptor) {
            List<ClassDesc> parameters = MethodTypeDesc.ofDescriptor(descriptor).parameterList();
            return at < parameters.size() && parameters.get(at).equals(parameter);
        }
    }

    /**
     * What a walk answered, written by name.
     *
     * <p>Every member the walk answered about arrives under the spelling its row is written with:
     * the name, where the name is one member, and the name with the overload told apart where it is
     * not. A member the population does not declare is a question this cannot answer — whether its
     * name holds others is read off the population — and it is refused rather than passed through
     * under a spelling nobody checked.
     *
     * @param answers what the walk answered, by owner, name and descriptor
     */
    <A> Map<String, A> by(Map<String, A> answers) {
        refuseTheNamesNothingTellsApart(answers.keySet(), answers);
        Map<String, A> written = new TreeMap<>();
        for (Map.Entry<String, A> answered : answers.entrySet()) {
            written.put(spelling(answered.getKey(), answers), answered.getValue());
        }
        return written;
    }

    /**
     * A refusal naming every member whose row nothing says the overload of, and not the first of
     * them.
     *
     * <p>A name told apart is one edit, and the names of a roster disagree in whatever number they
     * disagree in. Refusing on the first would be read as the whole of what the roster is short of,
     * and each round of saying which overload a row means would find the next one.
     */
    private void refuseTheNamesNothingTellsApart(Set<String> written, Map<String, ?> answers) {
        refuseSelectorsThatDoNotPickOneMemberEach();
        Set<String> nothingTellsApart = new TreeSet<>();
        for (String member : written) {
            if (!declared.contains(member)) {
                throw new AssertionError("`" + member + "` is not a member of the population this"
                        + " roster is written from, so whether its name holds others is a question"
                        + " this cannot answer");
            }
            if (spellingOf(member, answers) == null) {
                nothingTellsApart.add(member);
            }
        }
        if (!nothingTellsApart.isEmpty()) {
            throw new AssertionError("each of these is one of several members of its name, and the"
                    + " walk did not answer the same about the others — a row saying only the name"
                    + " would say this one's answer about the rest, so say which parameter tells"
                    + " them apart: " + nothingTellsApart);
        }
    }

    /**
     * The spelling {@code member}'s row is written with, and a refusal where nothing says which
     * overload it is.
     *
     * <p>A name whose overloads the walk answered alike is one member here and is spelt as itself.
     * A name whose overloads were answered differently is told apart or it is refused: a row
     * spelling only the name would carry one overload's answer under a name the others wear too,
     * which is the reading a roster of names is refused for.
     */
    private String spelling(String member, Map<String, ?> answers) {
        String written = spellingOf(member, answers);
        if (written == null) {
            throw new AssertionError("`" + member + "` is one of several members of its name and"
                    + " nothing says which of them a row means");
        }
        return written;
    }

    /** The same, and nothing where the name holds members the walk answered differently and no row
     *  says which of them this is. */
    private String spellingOf(String member, Map<String, ?> answers) {
        String called = calledOf(member);
        List<String> overloads = overloadsOf(called);
        if (overloads.size() == 1 || answeredAlike(overloads, answers)) {
            return called;
        }
        for (Told each : told) {
            if (each.names(called) && each.picks(descriptorOf(member))) {
                return each.spelt();
            }
        }
        return null;
    }

    /**
     * A refusal where what the rows of a name pick out is not one member each.
     *
     * <p>Both ways round, because a row saying which member it is is only that while it picks one
     * member and while that member is picked by it alone.
     *
     * <p>A row picking several says nothing of the kind: the members it picks would be written
     * under one spelling and whichever of them the walk answered last would be the answer the row
     * holds — which is the reading a roster of names is refused for, arriving through the thing
     * that was meant to stop it.
     *
     * <p>And a member picked by several rows is one whose spelling is whichever row was written
     * first. Two rows that both pick it are two claims about one member, and reading the list until
     * one matches settles them by the order somebody happened to write them in — so the member is
     * spelt as the sibling of whichever row won, and moves the first time the list is reordered.
     */
    private void refuseSelectorsThatDoNotPickOneMemberEach() {
        Map<String, List<String>> notOne = new TreeMap<>();
        Map<String, List<String>> pickedBy = new TreeMap<>();
        Map<String, Set<String>> under = new TreeMap<>();
        for (Told each : told) {
            List<String> overloads = overloadsOf(each.owner() + "#" + each.name());
            if (overloads.isEmpty()) {
                // A name this population does not declare. The rows of one roster are written for
                // whichever populations the rules that share them read, and a row about another
                // one is not about anything here — being short of nothing is not being stale.
                continue;
            }
            List<String> picked = overloads.stream()
                    .filter(member -> each.picks(descriptorOf(member))).toList();
            if (picked.size() != 1) {
                notOne.put(each.spelt(), picked);
            }
            for (String member : picked) {
                pickedBy.computeIfAbsent(member, _ -> new ArrayList<>()).add(each.spelt());
                under.computeIfAbsent(each.spelt(), _ -> new TreeSet<>()).add(member);
            }
        }
        if (!notOne.isEmpty()) {
            throw new AssertionError("a row says which member it is, and each of these picks out"
                    + " something else: several, where the parameter it names is one its siblings"
                    + " take as well, or none, where nothing of that name takes it any more. "
                    + notOne);
        }
        Map<String, List<String>> twice = new TreeMap<>();
        pickedBy.forEach((member, rows) -> {
            if (rows.size() > 1) {
                twice.put(member, rows);
            }
        });
        if (!twice.isEmpty()) {
            throw new AssertionError("each of these members is picked out by several rows, so"
                    + " which one it is written as is whichever of them was written first: say"
                    + " which member each row is for, once. " + twice);
        }
        Map<String, Set<String>> shared = new TreeMap<>();
        under.forEach((spelling, members) -> {
            if (members.size() > 1) {
                shared.put(spelling, members);
            }
        });
        if (!shared.isEmpty()) {
            throw new AssertionError("each of these spellings is what several members are written"
                    + " under, so the roster holds whichever of them was read last: what a row is"
                    + " spelt as has to say which member it is. " + shared);
        }
    }

    /** Whether the walk answered the same about every one of {@code overloads}. */
    private static boolean answeredAlike(List<String> overloads, Map<String, ?> answers) {
        Object first = answers.get(overloads.getFirst());
        for (String each : overloads) {
            Object answered = answers.get(each);
            if (first == null ? answered != null : !first.equals(answered)) {
                return false;
            }
        }
        return true;
    }

    /** Every member the population declares under {@code called}, as a walk's answer names one. */
    private List<String> overloadsOf(String called) {
        List<String> found = new ArrayList<>();
        for (String each : declared) {
            if (called.equals(calledOf(each))) {
                found.add(each);
            }
        }
        return found;
    }

    /**
     * A set of members that answers one way, written by name.
     *
     * <p>The same question as {@link #by} asked of a walk that answers whether rather than what, and
     * written through it so that a name held by a member the walk left out is told apart rather than
     * standing for it.
     *
     * @param answering the members the walk answered for, as owner, name and descriptor
     */
    List<String> namesOf(Set<String> answering) {
        Map<String, Boolean> answers = new LinkedHashMap<>();
        for (String each : declared) {
            answers.put(each, answering.contains(each));
        }
        refuseTheNamesNothingTellsApart(answering, answers);
        Set<String> written = new TreeSet<>();
        for (String each : answering) {
            written.add(spelling(each, answers));
        }
        return List.copyOf(written);
    }

    /**
     * A roster written here, in the order this hands one back.
     *
     * <p>What a roster says is which rows there are, and the order they come back in is a set's:
     * sorted by the spelling. Held to the order they were written in, a row would have to be moved
     * whenever its spelling sorted somewhere else — and where a spelling says a type, that is a row
     * moved for a type that was moved. The rows are what is being claimed; where each of them sits
     * among the others is not.
     */
    static List<String> asItHandsThemBack(List<String> written) {
        return written.stream().sorted().toList();
    }

    /** A type as a class file names it: the whole of it, with {@code /} between the steps. */
    private static String asAClassFileNamesIt(ClassDesc type) {
        String descriptor = type.descriptorString();
        return descriptor.startsWith("L") && descriptor.endsWith(";")
                ? descriptor.substring(1, descriptor.length() - 1) : descriptor;
    }

    /** What the member is called: its owner and its name, which is what its overloads share. */
    private static String calledOf(String member) {
        return member.substring(0, member.indexOf('('));
    }

    /** What it takes and answers with, which is what tells one overload of a name from another. */
    private static String descriptorOf(String member) {
        return member.substring(member.indexOf('('));
    }
}
