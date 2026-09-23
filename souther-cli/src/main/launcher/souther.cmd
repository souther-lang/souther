@echo off
rem Runs the shaded jar under this script's own directory on a Java the machine already has. It sits
rem where the other distribution's launcher sits, so whichever of the two was unpacked, the directory
rem to put on a path is the same one.
rem
rem -Xss is given the stack this compiler is supported on. What a definition may say is bounded
rem ([#source-structural-complexity-is-bounded]), and holding that bound is what the flag is for:
rem every phase descends what it builds by recursion, and a source at the bound needs about a
rem megabyte. The default is a platform's rather than this compiler's, so without the flag a source
rem that compiles here would depend on where it was compiled. The size, and the Java this refuses to
rem run below, are the root pom's `souther.jvm.stack` and `souther.java.minimum`, filled in when this
rem script is packaged.
rem
rem The version of the Java it found is read out of the `release` file of the image that Java belongs
rem to, rather than by starting it and asking. Asking costs a JVM start on every command run, and
rem this costs two file reads. A version read as a number below the one the classes in the jar were
rem written for is refused here, because what the JVM says instead names a class file version and
rem leaves the reader to work out which Java that was.
rem
rem Read as a number, and nothing else is read as anything. A Java can be reached through something
rem that is not its own image directory (a shim, a wrapper, a path a user assembled), an image can
rem carry no `release` at all, and one that carries it can state a version this does not understand.
rem A launcher that refused whatever it could not account for would refuse a working Java, and one
rem that compared whatever it found would be comparing text, which puts the refusal on which letters
rem sort under a two. So the comparison is reached only by a run of digits, and every other reading
rem gets what it would have got had nothing been read at all.
setlocal

set "java=java.exe"
set "image="
if defined JAVA_HOME set "java=%JAVA_HOME%\bin\java.exe"
if defined JAVA_HOME set "image=%JAVA_HOME%"
if defined JAVA_HOME if not exist "%java%" goto :nojava

if not defined JAVA_HOME for /f "delims=" %%p in ('where java.exe 2^>nul') do if not defined onpath set "onpath=%%p"
if not defined JAVA_HOME if not defined onpath goto :nojava
if not defined JAVA_HOME call :imageholding "%onpath%"

rem Each step below leaves for :run rather than guarding the comparison with a condition beside it. A
rem variable is put into a line before any of that line's conditions is weighed, so a comparison
rem written behind a guard has nothing on its left the moment there is nothing to compare.
rem
rem The second step is what makes the third a comparison of numbers: the digits are the delimiters,
rem so a version that is a run of them yields no word to iterate over and the line does nothing,
rem while anything else yields one and leaves.
set "major="
if defined image if exist "%image%\release" for /f "usebackq tokens=2 delims==" %%v in (`findstr /b /c:"JAVA_VERSION=" "%image%\release"`) do call :majorof %%v
if not defined major goto :run
for /f "delims=0123456789" %%x in ("%major%") do goto :run
if %major% LSS @souther.java.minimum@ goto :oldjava

:run
"%java%" -Xss@souther.jvm.stack@ -jar "%~dp0lib\souther.jar" %*
exit /b %ERRORLEVEL%

rem The image is the directory the `bin` holding that java is in.
:imageholding
for %%d in ("%~dp1..") do set "image=%%~fd"
exit /b

rem A release states its version the way Java numbers them, so the part before the first dot is the
rem one that has to be at least the minimum. An eight states 1.8, and answers this question with a one.
:majorof
set "stated=%~1"
for /f "tokens=1 delims=." %%m in ("%stated%") do set "major=%%m"
exit /b

:nojava
1>&2 echo souther found no Java: set JAVA_HOME to a JDK @souther.java.minimum@, or put its java on PATH. A JDK rather
1>&2 echo than a JRE, because `souther japi` reads javadoc through a compiler. The distribution
1>&2 echo without `nojdk` in its name carries a runtime of its own and needs neither.
exit /b 1

:oldjava
1>&2 echo souther needs Java @souther.java.minimum@ and "%image%" states Java %major%. Point JAVA_HOME at a JDK @souther.java.minimum@, or
1>&2 echo put its java on PATH. The distribution without `nojdk` in its name carries a runtime of
1>&2 echo its own and needs neither.
exit /b 1
