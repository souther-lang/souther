@echo off
rem Runs the shaded jar beside this script on a Java the machine already has. The distribution that
rem carries a Java of its own has a launcher of its own and does not use this one.
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

"%java%" -Xss4m -jar "%~dp0..\lib\souther.jar" %*
exit /b %ERRORLEVEL%

:nojava
1>&2 echo souther needs Java 25 and found none: set JAVA_HOME to a Java 25 installation, or put
1>&2 echo java on PATH. The distribution without `nojre` in its name carries a Java of its own
1>&2 echo and needs neither.
exit /b 1
