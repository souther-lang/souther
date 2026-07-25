// The two failures that are not domain outcomes, mapped once for the whole boundary.
//
// A rejected input never reaches a behavior, so it cannot be a case: DecodeFailed carries Raoh's issues
// (path, code, message) and becomes a 400, the same treatment Spring gives its own binding failures.
//
// A platform failure is not a case either (ADR-0029). The jOOQ implementation does not catch it, Souther
// passes it through untouched, and it arrives here as a DataAccessException — 503. Spring Boot's jOOQ
// autoconfig enables exception translation, which is what turns jOOQ's own exception into that type.
package app.issuetracker.web

import app.issuetracker.souther.DecodeFailed

import org.springframework.dao.DataAccessException
import org.springframework.http.HttpStatus
import org.springframework.http.ResponseEntity
import org.springframework.web.bind.annotation.ExceptionHandler
import org.springframework.web.bind.annotation.RestControllerAdvice

@RestControllerAdvice
class BoundaryErrors {

    @ExceptionHandler(DecodeFailed::class)
    fun onDecodeFailed(e: DecodeFailed): ResponseEntity<Any> =
        ResponseEntity.badRequest().body(mapOf("issues" to e.issues.toJsonList()))

    @ExceptionHandler(DataAccessException::class)
    fun onPlatformFailure(e: DataAccessException): ResponseEntity<Any> =
        ResponseEntity.status(HttpStatus.SERVICE_UNAVAILABLE)
            .body(mapOf("error" to "storage_unavailable"))
}
