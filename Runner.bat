@ECHO OFF
SET "RunnerName=Runner for UWC"
TITLE %RunnerName%
CD /D "%~DP0"
CLS
GOTO SSS

:SSS
IF EXIST "%WINDIR%\PY.EXE" (%WINDIR%\py.exe UWC.py) ELSE (GOTO E)
ECHO %RunnerName%: %%ERRORLEVEL%% = %ERRORLEVEL%
ECHO %RunnerName%: The sub-process has exited, if you want to run it again, press any key to continue, otherwise just please close this window. 
PAUSE>NUL
GOTO SSS

:E
START /REALTIME "" "https://blog.csdn.net/weixin_51485807/article/details/123085336?spm=1001.2014.3001.5501"
ECHO %RunnerName%: No py.exe detected, please configure first. 
ECHO %RunnerName%: Press any key to exit. 
PAUSE>NUL
EXIT /B