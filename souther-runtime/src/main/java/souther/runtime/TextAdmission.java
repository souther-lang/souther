package souther.runtime;

/**
 * What asking whether text from outside is a {@code String} answers (spec §what-a-string-holds).
 *
 * <p>Two refusals and not one, because a door that says why it refused says something different for
 * each: text that is not a sequence of scalar values is not text, and text whose canonical value is
 * longer than the carrier declares a {@code String} to hold is text that has no place. What each door
 * makes of them is the door's; that they are told apart is not.
 */
public sealed interface TextAdmission {

    /** The text, as the {@code String} it is: canonical, and within what the carrier holds. */
    record Admitted(String text) implements TextAdmission {}

    /** Text holding half of a surrogate pair, which starts at {@code at} in UTF-16 units. */
    record NotText(int at) implements TextAdmission {}

    /** Text whose canonical value is longer than a {@code String} holds. */
    record NoPlace() implements TextAdmission {}
}
