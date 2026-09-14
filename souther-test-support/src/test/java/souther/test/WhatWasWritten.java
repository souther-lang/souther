package souther.test;

/**
 * Declarations written the ways a reading of them has to tell apart.
 *
 * <p>A fixture, so that what the reading answers is held to shapes somebody wrote on purpose rather
 * than to whatever a module happens to hold today.
 */
final class WhatWasWritten {

    /** A field and a method of one name, which are two things the author wrote. */
    private final String beside = "";

    String beside() {
        return beside + "!";
    }

    /** A component, written as itself, a field and an accessor. */
    record Stating(String stated) {}

    /** A component with an overload beside it, which is a second declaration of the name. */
    record Counting(int counted) {

        int counted(int by) {
            return counted + by;
        }
    }
}
