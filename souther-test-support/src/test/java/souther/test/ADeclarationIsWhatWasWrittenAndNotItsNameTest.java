package souther.test;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A declaration is what was written, and not the name it goes by.
 *
 * <p>{@link WhatAModuleDeclares#taking} is asked which declarations take a name, and a check
 * reading it decides from every one of them. Answering one per name would let the second
 * declaration of a name pass behind the first — and the one that passes is whichever the class file
 * happens to list earlier, which is not a thing anybody chose.
 *
 * <p>What is left out is the two a record's component is written as. The compiler writes a field of
 * the component's name and descriptor and an accessor that takes nothing and answers its type; a
 * class file says which those are, so leaving them out is telling a component from a member rather
 * than collapsing the two by their name. An overload beside the component is a member.
 *
 * <p>Held here rather than in each check that reads it. What a module's classes hold is that
 * module's to say; that the reading names every declaration is the mechanism's, and a check made to
 * prove it again would be proving it over whatever its module happened to hold.
 */
class ADeclarationIsWhatWasWrittenAndNotItsNameTest {

    /** A field and a method of one name are two declarations. */
    @Test
    void aFieldAndAMethodOfOneNameAreTwo() {
        assertEquals(List.of("FIELD", "METHOD"), kindsTaking("beside"));
    }

    /** A record component is one, and the field and accessor written for it are not beside it. */
    @Test
    void aComponentIsWrittenAsThreeThingsAndIsOne() {
        assertEquals(List.of("RECORD_COMPONENT"), kindsTaking("stated"));
    }

    /** And an overload beside a component is a declaration of its own. */
    @Test
    void andAnOverloadBesideAComponentIsItsOwn() {
        assertEquals(List.of("RECORD_COMPONENT", "METHOD"), kindsTaking("counted"));
    }

    private static List<String> kindsTaking(String name) {
        return WhatAModuleDeclares.of(WhatWasWritten.class).taking(Set.of(name)).stream()
                .filter(each -> each.ownerName().startsWith("souther/test/WhatWasWritten"))
                .map(each -> each.kind().name())
                .toList();
    }
}
