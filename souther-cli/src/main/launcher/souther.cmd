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
rem
rem The version of the Java it found is read out of the `release` file of the image that Java belongs
rem to, rather than by starting it and asking. Asking costs a JVM start on every command run, and
rem this costs two file reads. A version below the one the classes in the jar were written for is
rem refused here, because what the JVM says instead names a class file version and leaves the reader
rem to work out which Java that was.
rem
rem Not being able to read it is not a refusal. A Java can be reached through something that is not
rem its own image directory — a shim, a wrapper, a path a user assembled — and a launcher that
rem refused whatever it could not account for would refuse a working Java. Such a run gets what it
rem would have got had nothing been read at all.
setlocal

set "java=java.exe"
set "image="
if defined JAVA_HOME set "java=%JAVA_HOME%\bin\java.exe"
if defined JAVA_HOME set "image=%JAVA_HOME%"
if defined JAVA_HOME if not exist "%java%" goto :nojava

if not defined JAVA_HOME for /f "delims=" %%p in ('where java.exe 2^>nul') do if not defined onpath set "onpath=%%p"
if not defined JAVA_HOME if not defined onpath goto :nojava
if not defined JAVA_HOME call :imageholding "%onpath%"

set "major="
if defined image if exist "%image%\release" for /f "usebackq tokens=2 delims==" %%v in (`findstr /b /c:"JAVA_VERSION=" "%image%\release"`) do call :majorof %%v
if defined major if %major% LSS 25 goto :oldjava

"%java%" -Xss4m -jar "%~dp0lib\souther.jar" %*
exit /b %ERRORLEVEL%

rem The image is the directory the `bin` holding that java is in.
:imageholding
for %%d in ("%~dp1..") do set "image=%%~fd"
exit /b

rem A release states its version the way Java numbers them, so the part before the first dot is the
rem one that has to be 25 or more. An eight states 1.8, and answers this question with a one.
:majorof
set "stated=%~1"
for /f "tokens=1 delims=." %%m in ("%stated%") do set "major=%%m"
exit /b

:nojava
1>&2 echo souther found no Java: set JAVA_HOME to a JDK 25, or put its java on PATH. A JDK rather
1>&2 echo than a JRE, because `souther japi` reads javadoc through a compiler. The distribution
1>&2 echo without `nojdk` in its name carries a runtime of its own and needs neither.
exit /b 1

:oldjava
1>&2 echo souther needs Java 25 and "%image%" states Java %major%. Point JAVA_HOME at a JDK 25, or
1>&2 echo put its java on PATH. The distribution without `nojdk` in its name carries a runtime of
1>&2 echo its own and needs neither.
exit /b 1
