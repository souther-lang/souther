package souther.compiler.semantics;

/**
 * What an operation gathering into a set gathers of what it is handed: the value itself, or every
 * element the value holds.
 */
public enum WhatIsGathered {
    THE_VALUE,
    EVERY_ELEMENT
}
