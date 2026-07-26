// Boots Spring for real (RANDOM_PORT brings up embedded Tomcat), connects to H2, and drives every route
// over real HTTP: Tomcat -> Jackson -> the Kotlin controller -> a behavior -> jOOQ -> H2 -> JSON.
//
// The three failure kinds are each checked, because telling them apart is the point of the boundary:
// NoLabels is a domain outcome (a returned case) and becomes 400 with an error name; an invariant
// violation on input is a decode failure and becomes 400 with Raoh's issues and their paths; a dropped
// table is a platform failure, which is no case at all — it passes through Souther as an exception and
// becomes 503.
package app.issuetracker

import org.jooq.DSLContext

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test

import org.springframework.beans.factory.annotation.Autowired
import org.springframework.boot.test.context.SpringBootTest
import org.springframework.core.env.Environment
import org.springframework.http.MediaType
import org.springframework.test.annotation.DirtiesContext
import org.springframework.test.web.servlet.client.RestTestClient

@SpringBootTest(webEnvironment = SpringBootTest.WebEnvironment.RANDOM_PORT)
class IssueTrackerApiTest {

    @Autowired
    lateinit var dsl: DSLContext

    @Autowired
    lateinit var env: Environment

    private lateinit var client: RestTestClient

    @BeforeEach
    fun reset() {
        // The context — and so the in-memory DB — is shared across tests, so each test starts from
        // the seeded state of data.sql.
        dsl.deleteFrom(ISSUE_LABELS).execute()
        dsl.deleteFrom(ISSUES).execute()
        insertIssue("i-1", "crash on save", "kawasima", "bug", "ui")
        insertIssue("i-2", "typo in the footer", null, "bug")

        val port = env.getRequiredProperty("local.server.port")
        client = RestTestClient.bindToServer().baseUrl("http://localhost:$port").build()
    }

    @Test
    fun `an issue is returned with its label set and assignee`() {
        client.get().uri("/issues/i-1").exchange()
            .expectStatus().isOk()
            .expectBody()
            // A Set encodes to a JSON array whose order is unspecified; the comparison is order-insensitive.
            .json("""{"id":"i-1","title":"crash on save","labels":["bug","ui"],"assignee":"kawasima"}""")
    }

    @Test
    fun `an unknown issue is not found`() {
        client.get().uri("/issues/nope").exchange().expectStatus().isNotFound()
    }

    @Test
    fun `the optional assignee is opened by the domain`() {
        client.get().uri("/issues/i-1/assignee").exchange()
            .expectStatus().isOk()
            .expectBody().json("""{"name":"kawasima"}""")

        // i-2 has no assignee: assigneeOf takes its None arm, which the boundary folds to 204.
        client.get().uri("/issues/i-2/assignee").exchange().expectStatus().isNoContent()
    }

    @Test
    fun `attaching a label adds it to the set and stores it`() {
        postJson("/issues/i-2/labels", """{"label":"ui"}""")
            .expectStatus().isOk()
            .expectBody().json("""{"id":"i-2","labels":["bug","ui"]}""")

        assertEquals(setOf("bug", "ui"), labelsOf("i-2"), "the label set is stored")
    }

    @Test
    fun `attaching a label already carried changes nothing`() {
        postJson("/issues/i-1/labels", """{"label":"bug"}""")
            .expectStatus().isOk()

        assertEquals(setOf("bug", "ui"), labelsOf("i-1"), "a Set insert of a member is a no-op")
    }

    @Test
    fun `attaching to an unknown issue is not found and writes nothing`() {
        postJson("/issues/nope/labels", """{"label":"ui"}""")
            .expectStatus().isNotFound()

        assertEquals(3, dsl.fetchCount(ISSUE_LABELS), "no label row was added")
    }

    @Test
    fun `detaching a label removes it from the set`() {
        client.delete().uri("/issues/i-1/labels/ui").exchange()
            .expectStatus().isOk()
            .expectBody().json("""{"id":"i-1","labels":["bug"]}""")

        assertEquals(setOf("bug"), labelsOf("i-1"))
    }

    @Test
    fun `opening an issue normalizes the raw label text`() {
        postJson("/issues", """{"id":"i-3","title":"flaky test","labels":"Bug, bug , UI"}""")
            .expectStatus().isCreated()
            .expectBody().json("""{"id":"i-3","labels":["bug","ui"]}""")

        // Case and spacing collapsed, and the duplicate did not survive the Set.
        assertEquals(setOf("bug", "ui"), labelsOf("i-3"))
    }

    @Test
    fun `no surviving label is a domain outcome, and nothing is written`() {
        postJson("/issues", """{"id":"i-4","title":"whitespace","labels":" , "}""")
            .expectStatus().isBadRequest()
            .expectBody().json("""{"error":"no_labels"}""")

        assertEquals(0, dsl.fetchCount(ISSUES, ID.eq("i-4")), "openIssue returned before writing")
    }

    @Test
    fun `an invariant violation is rejected by the decoder, before any behavior runs`() {
        // Label's invariant is length >= 1, so an empty label never becomes a domain value. The
        // rule reaches the boundary as the Raoh constraint that states it, so the issue names what
        // was broken — `too_short` at `/label`, not one code shared by every invariant.
        postJson("/issues/i-1/labels", """{"label":""}""")
            .expectStatus().isBadRequest()
            .expectBody()
            .jsonPath("$.issues[0].path").isEqualTo("/label")
            .jsonPath("$.issues[0].code").isEqualTo("too_short")

        assertEquals(setOf("bug", "ui"), labelsOf("i-1"), "the label set is untouched")
    }

    @Test
    fun `the labels two issues share are their intersection`() {
        client.get().uri("/issues/i-1/shared-labels/i-2").exchange()
            .expectStatus().isOk()
            .expectBody().json("""{"labels":["bug"]}""")
    }

    @Test
    fun `every label is counted across the board`() {
        client.get().uri("/labels/counts").exchange()
            .expectStatus().isOk()
            .expectBody().json("""{"counts":{"bug":2,"ui":1}}""")
    }

    @Test
    fun `the ranking leads with the most-used label`() {
        client.get().uri("/labels/top?n=1").exchange()
            .expectStatus().isOk()
            .expectBody().json("""{"labels":["bug"]}""")
    }

    @Test
    fun `only the labels the board leans on survive the threshold`() {
        client.get().uri("/labels/busy?atLeast=2").exchange()
            .expectStatus().isOk()
            .expectBody().json("""{"counts":{"bug":2}}""")

        client.get().uri("/labels/busy?atLeast=9").exchange()
            .expectStatus().isOk()
            .expectBody().json("""{"counts":{}}""")
    }

    // Dropping the table reproduces a database failure, so the context is rebuilt afterwards rather than
    // handing a broken schema to later tests. The isolation rests on three facts together: H2 keeps the
    // in-memory DB to JVM exit (DB_CLOSE_DELAY=-1), so @DirtiesContext rebuilds the Spring context but not
    // the DB; and the restart re-runs schema.sql (CREATE TABLE IF NOT EXISTS) and data.sql under
    // spring.sql.init.mode=always, which brings the dropped table back.
    @DirtiesContext(methodMode = DirtiesContext.MethodMode.AFTER_METHOD)
    @Test
    fun `a platform failure is no case at all, and passes through as 503`() {
        dsl.execute("DROP TABLE issue_labels")

        client.get().uri("/labels/counts").exchange()
            .expectStatus().isEqualTo(503)
            .expectBody().json("""{"error":"storage_unavailable"}""")
    }

    private fun postJson(uri: String, json: String) =
        client.post().uri(uri).contentType(MediaType.APPLICATION_JSON).body(json).exchange()

    private fun insertIssue(id: String, title: String, assignee: String?, vararg labels: String) {
        dsl.insertInto(ISSUES).set(ID, id).set(TITLE, title).set(ASSIGNEE, assignee).execute()
        labels.forEach { dsl.insertInto(ISSUE_LABELS).set(ISSUE_ID, id).set(LABEL, it).execute() }
    }

    private fun labelsOf(id: String): Set<String> =
        dsl.select(LABEL).from(ISSUE_LABELS).where(ISSUE_ID.eq(id)).fetchSet(LABEL)
}
