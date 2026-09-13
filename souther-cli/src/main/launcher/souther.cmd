@echo off
rem Runs the shaded jar under this script's own directory on a Java the machine already has. It sits
rem where the other distribution's launcher sits, so whichever of the two was unpacked, the directory
rem to put on a path is the same one.
rem
rem -Xss4m is the stack this compiler is supported on. What a definition may say is bounded
rem ([#source-structural-complexity-is-bounded]), and holding that bound is what the flag is for:
rem every phase descends what it builds by recursion, and a source at the bound needs about a
rem megabyte. The default is a platform's rather than this compiler's, so without the flag a source
rem that compiles here would depend on where it was compiled.
setlocal

set "java=java.exe"
if defined JAVA_HOME set "java=%JAVA_HOME%\bin\java.exe"
if defined JAVA_HOME if not exist "%java%" goto :nojava
if not defined JAVA_HOME where java.exe >nul 2>&1 || goto :nojava

"%java%" -Xss4m -jar "%~dp0lib\souther.jar" %*
exit /b %ERRORLEVEL%

:nojava
1>&2 echo souther found no Java: set JAVA_HOME to a JDK 25, or put its java on PATH. A JDK rather
1>&2 echo than a JRE, because `souther japi` reads javadoc through a compiler. The distribution
1>&2 echo without `nojdk` in its name carries a runtime of its own and needs neither.
exit /b 1
