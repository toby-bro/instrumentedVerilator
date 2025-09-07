import "DPI-C" function string V3Os_getenvStr(input string envvar, input string defaultVal);
import "DPI-C" function void   V3Os_setenvStr(input string envvar, input string value, input string why);
import "DPI-C" function string V3Os_filenameCleanup(input string filename);
import "DPI-C" function string V3Os_filenameDir(input string filename);
import "DPI-C" function string V3Os_filenameExt(input string filename);
import "DPI-C" function string V3Os_filenameNonDir(input string filename);
import "DPI-C" function string V3Os_filenameNonDirExt(input string filename);
import "DPI-C" function string V3Os_filenameSubstitute(input string filename);
import "DPI-C" function string V3Os_filenameRealPath(input string filename);
import "DPI-C" function string V3Os_filenameRelativePath(input string filename, input string base);
import "DPI-C" function bit    V3Os_filenameIsRel(input string filename);
import "DPI-C" function string V3Os_filenameSlashPath(input string path);
import "DPI-C" function void   V3Os_createDir(input string dirname);
import "DPI-C" function void   V3Os_filesystemFlush(input string dirname);
import "DPI-C" function void   V3Os_filesystemFlushBuildDir(input string dirname);
import "DPI-C" function void   V3Os_unlinkRegexp(input string dir, input string regexp);
import "DPI-C" function longint unsigned V3Os_rand64(inout longint unsigned stater[2]);
import "DPI-C" function string V3Os_trueRandom(input int size);
import "DPI-C" function longint unsigned V3Os_timeUsecs();
import "DPI-C" function void   V3Os_u_sleep(input longint signed usec);
import "DPI-C" function int    V3Os_system(input string cmd);
module getenvStr_mod(input string envvar, input string defaultVal, output string result);
  always_comb result = V3Os_getenvStr(envvar, defaultVal);
endmodule
module setenvStr_mod(input string envvar, input string value, input string why, output bit ok);
  always_comb begin
    V3Os_setenvStr(envvar, value, why);
    ok = 1;
  end
endmodule
module filenameCleanup_mod(input string filename, output string cleaned);
  always_comb cleaned = V3Os_filenameCleanup(filename);
endmodule
module filenameDir_mod(input string filename, output string dir);
  always_comb dir = V3Os_filenameDir(filename);
endmodule
module filenameExt_mod(input string filename, output string ext);
  always_comb ext = V3Os_filenameExt(filename);
endmodule
module filenameNonDir_mod(input string filename, output string nonDir);
  always_comb nonDir = V3Os_filenameNonDir(filename);
endmodule
module filenameNonDirExt_mod(input string filename, output string nonDirExt);
  always_comb nonDirExt = V3Os_filenameNonDirExt(filename);
endmodule
module filenameSubstitute_mod(input string filename, output string substituted);
  always_comb substituted = V3Os_filenameSubstitute(filename);
endmodule
module filenameRealPath_mod(input string filename, output string realpath);
  always_comb realpath = V3Os_filenameRealPath(filename);
endmodule
module filenameRelativePath_mod(input string filename, input string base, output string relpath);
  always_comb relpath = V3Os_filenameRelativePath(filename, base);
endmodule
module filenameIsRel_mod(input string filename, output bit isRelative);
  always_comb isRelative = V3Os_filenameIsRel(filename);
endmodule
module filenameSlashPath_mod(input string path, output string slashPath);
  always_comb slashPath = V3Os_filenameSlashPath(path);
endmodule
module createDir_mod(input string dirname, output bit created);
  always_comb begin
    V3Os_createDir(dirname);
    created = 1;
  end
endmodule
module filesystemFlush_mod(input string dirname, output bit flushed);
  always_comb begin
    V3Os_filesystemFlush(dirname);
    flushed = 1;
  end
endmodule
module filesystemFlushBuildDir_mod(input string dirname, output bit flushed);
  always_comb begin
    V3Os_filesystemFlushBuildDir(dirname);
    flushed = 1;
  end
endmodule
module unlinkRegexp_mod(input string dir, input string regexp, output bit success);
  always_comb begin
    V3Os_unlinkRegexp(dir, regexp);
    success = 1;
  end
endmodule
module rand64_mod(input longint unsigned st0, input longint unsigned st1,
                  output longint unsigned result, output longint unsigned new0, output longint unsigned new1);
  longint unsigned stater[2];
  always_comb begin
    stater[0] = st0;
    stater[1] = st1;
    result = V3Os_rand64(stater);
    new0   = stater[0];
    new1   = stater[1];
  end
endmodule
module trueRandom_mod(input int size, output string randomStr);
  always_comb randomStr = V3Os_trueRandom(size);
endmodule
module timeUsecs_mod(output longint unsigned usecs);
  always_comb usecs = V3Os_timeUsecs();
endmodule
module u_sleep_mod(input longint signed usec, output bit slept);
  always_comb begin
    V3Os_u_sleep(usec);
    slept = 1;
  end
endmodule
module system_mod(input string cmd, output int exitcode);
  always_comb exitcode = V3Os_system(cmd);
endmodule
