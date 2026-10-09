package souther.compiler.proof;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.ClosurePositions;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.Unsayable;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What a closing of an operation the library writes is about, proved against its body.
 *
 * <p>A closing names a proposition the domain has no words for, and some of those are about the
 * operation's own arguments: that no two elements of a container come to one answer of a closure
 * is about which container and which closure. The body shows which by how it comes to the
 * proposition — with nothing else in the way, so that what a reader takes of the closing, where it
 * is about those two, is what the body answers.
 */
public final class WhatAClosingIsAbout {

    private final Library library;
    private final Set<ValueName.Stdlib.Operation> readThrough;

    /**
     * @param readThrough the operations whose bodies are read where they are called, as the
     *                    proofs of what the library's operations come to read them
     */
    public WhatAClosingIsAbout(Library library, Set<ValueName.Stdlib.Operation> readThrough) {
        this.library = library;
        this.readThrough = Set.copyOf(readThrough);
    }

    /**
     * Whether {@code operation} comes out true exactly where no two elements of its argument at
     * {@code container} come to one answer of its closure at {@code closure}: where its body says
     * that container holds as many as a set holds that is made of the closure's answer on each of
     * its elements, once each — and says nothing else.
     *
     * <p>As many different answers as elements is every element's answer different from every
     * other's. The set is known only by what its size comes to, how many different values the list
     * it was made of holds ({@link Unsayable#HOW_MANY_DIFFERENT_VALUES}); the list is known only by
     * what it is settled to build, one answer of that closure for each element of that container.
     */
    public LibraryProver.Outcome noTwoAlike(ValueName.Stdlib.Operation operation, int container,
                                            int closure) {
        Reading reading = new Reading(library, readThrough);
        try {
            List<Value> params = new ArrayList<>();
            for (int at = 0; at < library.takes(operation).size(); at++) {
                params.add(new Value.Argument(at));
            }
            List<Reading.Case> cases = reading.cases(reading.bodyOf(operation),
                    new Reading.Frame(params, Map.of()));
            if (cases.size() != 1 || !(cases.getFirst().when()
                    instanceof LawProposition.Always<Value>(boolean always)) || !always
                    || !(cases.getFirst().is() instanceof Value.Statement(
                            LawProposition.Compared<Value>(var form, Rel states)))
                    || states != Rel.EQ || form.constant().signum() != 0
                    || form.coefs().size() != 2) {
                return notThat();
            }
            Value theContainer = new Value.Argument(container);
            Value set = null;
            ExactRatio ofTheContainer = null;
            ExactRatio ofTheSet = null;
            for (Map.Entry<LawNumber<Value>, ExactRatio> term : form.coefs().entrySet()) {
                if (!(term.getKey() instanceof LawNumber.SizeOf<Value>(
                        LawSubject.Argument<Value>(Value counted)))) {
                    return notThat();
                }
                if (counted.equals(theContainer)) {
                    ofTheContainer = term.getValue();
                } else {
                    set = counted;
                    ofTheSet = term.getValue();
                }
            }
            if (set == null || ofTheContainer == null
                    || !ofTheContainer.negated().equals(ofTheSet)
                    || !(set instanceof Value.Made(ValueName.Stdlib.Operation makes,
                            List<Value> handed))
                    || handed.size() != 1
                    || !(library.settled(makes, OperationLaw.Observed.SIZE)
                            instanceof Library.Settled.Unsaid(Unsayable why))
                    || why != Unsayable.HOW_MANY_DIFFERENT_VALUES
                    || !eachAnswered(operation, handed.getFirst(), theContainer, closure,
                            reading)) {
                return notThat();
            }
            reading.took(Proof.Used.law(makes, OperationLaw.Observed.SIZE));
            return new LibraryProver.Outcome.Proved(new Proof.ByTheBody(operation,
                    reading.used()));
        } catch (Reading.Stopped stopped) {
            return LibraryProver.stoppedAt(stopped);
        }
    }

    /** Whether {@code list} is settled to hold the answer of {@code operation}'s closure at
     *  {@code closure} on each element of {@code container}, once each. */
    private boolean eachAnswered(ValueName.Stdlib.Operation operation, Value list,
                                 Value container, int closure, Reading reading) {
        if (!(list instanceof Value.Made(ValueName.Stdlib.Operation maps, List<Value> args))) {
            return false;
        }
        BuiltFrom<Integer> built = library.builtFrom(maps);
        Integer each = built == null ? null : built.mapsEachElementOf();
        ClosurePositions theirs = library.positions(maps);
        ClosurePositions mine = library.positions(operation);
        if (each == null || theirs == null || mine == null
                || !args.get(each).equals(container)
                || !args.get(theirs.closureArg()).equals(new Value.Argument(closure))
                || theirs.elementParam() != mine.elementParam()
                || theirs.keyParam() != mine.keyParam()) {
            return false;
        }
        reading.took(new Proof.Used(maps, Proof.Taken.WHAT_IT_BUILDS));
        return true;
    }

    private static LibraryProver.Outcome notThat() {
        return new LibraryProver.Outcome.Open(
                new Unproved.DoesNotFollow(Unproved.Obligation.THE_STATEMENT));
    }
}
