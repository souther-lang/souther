package souther.compiler.meaning;

import souther.compiler.inputs.TermPath;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * Which case a value is, read where it stands: the value a {@code match} chooses its arm by, and
 * what the body of a behavior a call names answers, read where the call stands.
 *
 * <p>Only which case, and nothing else it might be asked: a value matched on is asked that, and
 * what the value holds is a question of what made it.
 */
public sealed interface WhichCase {

    /** What a dependency the row stands in answered, whichever case that is. */
    record AtAnAnswer(DecisionSubject.AnAnswer answer) implements WhichCase {

        public AtAnAnswer {
            Objects.requireNonNull(answer, "a dependency answered at some call");
        }
    }

    /** One of {@code cases}, whatever the input: a value the body writes out, or a name standing
     *  for one of several it does. */
    record Written(Set<TypeSymbol> cases) implements WhichCase {

        public Written {
            cases = Set.copyOf(cases);
            if (cases.isEmpty()) {
                throw new IllegalArgumentException("a value written out is of some case");
            }
        }
    }

    /** What stands at {@code at} of the input, whichever case that is. */
    record AtAnInput(TermPath at) implements WhichCase {

        public AtAnInput {
            Objects.requireNonNull(at, "a value of the input stands somewhere");
        }
    }

    /** Not read, and why. */
    record Unread(WhyUnread why) implements WhichCase {

        public Unread {
            Objects.requireNonNull(why, "a value is left unread for some reason");
        }
    }

    /**
     * One of several values, each answered where it is reached. The arms exclude each other: each
     * holds of a run that takes it and of no other.
     */
    record ByItsArms(List<Arm> arms) implements WhichCase {

        public ByItsArms {
            arms = List.copyOf(arms);
            if (arms.isEmpty()) {
                throw new IllegalArgumentException("a value chosen by arms has an arm");
            }
        }
    }

    /**
     * One arm: where a run reaches it, and what it answers there.
     *
     * @param reached whether a run takes this arm, every arm before it written in
     */
    record Arm(Derivation reached, WhichCase answers) {

        public Arm {
            Objects.requireNonNull(reached, "an arm is reached somewhere");
            Objects.requireNonNull(answers, "an arm answers something");
        }
    }
}
