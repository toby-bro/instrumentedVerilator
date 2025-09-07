import "DPI-C" function bit VString_wildmatchi(input string s, input string p);
import "DPI-C" function bit VString_wildmatch(input string s, input string p);
import "DPI-C" function string VString_dot(input string a, input string dot_, input string b);
import "DPI-C" function string VString_downcase(input string str);
import "DPI-C" function string VString_upcase(input string str);
import "DPI-C" function string VString_quoteAny(input string str, byte tgt, byte esc);
import "DPI-C" function string VString_dequotePercent(input string str);
import "DPI-C" function string VString_quoteStringLiteralForShell(input string str);
import "DPI-C" function string VString_escapeStringForPath(input string str);
import "DPI-C" function string VString_unquoteSVString(input string text, output string errOut);
import "DPI-C" function string VString_removeWhitespace(input string str);
import "DPI-C" function string VString_trimWhitespace(input string str);
import "DPI-C" function bit VString_isIdentifier(input string str);
import "DPI-C" function bit VString_isWhitespace(input string str);
import "DPI-C" function int VString_leadingWhitespaceCount(input string str);
import "DPI-C" function real VString_parseDouble(input string str, output bit success);
import "DPI-C" function string VString_replaceSubstr(input string str, input string from, input string to);
import "DPI-C" function string VString_replaceWord(input string str, input string from, input string to);
import "DPI-C" function bit VString_startsWith(input string str, input string prefix);
import "DPI-C" function bit VString_endsWith(input string str, input string suffix);
import "DPI-C" function string VString_aOrAn(input string word);
import "DPI-C" function longint VString_hashMurmur(input string str);
import "DPI-C" function string VName_dehash(input string in);
import "DPI-C" function string VName_hashedName();
import "DPI-C" function string VHashSha256_digestHex();
import "DPI-C" function string VHashSha256_digestSymbol();
import "DPI-C" function int VSpellCheck_editDistance(input string s, input string t);
import "DPI-C" function int VSpellCheck_cutoffDistance(input int goal_len, input int candidate_len);
import "DPI-C" function string VSpellCheck_bestCandidateInfo(input string goal, output int distancer);
module wildmatchi_mod(input string s, input string p, output logic match);
  always_comb begin
    match = VString_wildmatchi(s, p);
  end
endmodule
module wildmatch_mod(input string s, input string p, output logic match);
  always_comb begin
    match = VString_wildmatch(s, p);
  end
endmodule
module wildmatch_str_mod(input string s, input string p, output logic match);
  always_comb begin
    match = VString_wildmatch(s, p);
  end
endmodule
module dot_mod(input string a, input string dot_, input string b, output string out);
  always_comb begin
    out = VString_dot(a, dot_, b);
  end
endmodule
module downcase_mod(input string in, output string out);
  always_comb begin
    out = VString_downcase(in);
  end
endmodule
module upcase_mod(input string in, output string out);
  always_comb begin
    out = VString_upcase(in);
  end
endmodule
module quote_any_mod(input string in, input byte tgt, input byte esc, output string out);
  always_comb begin
    out = VString_quoteAny(in, tgt, esc);
  end
endmodule
module dequote_percent_mod(input string in, output string out);
  always_comb begin
    out = VString_dequotePercent(in);
  end
endmodule
module quote_shell_mod(input string in, output string out);
  always_comb begin
    out = VString_quoteStringLiteralForShell(in);
  end
endmodule
module escape_path_mod(input string in, output string out);
  always_comb begin
    out = VString_escapeStringForPath(in);
  end
endmodule
module unquote_sv_mod(input string in, output string out, output string err);
  always_comb begin
    out = VString_unquoteSVString(in, err);
  end
endmodule
module remove_ws_mod(input string in, output string out);
  always_comb begin
    out = VString_removeWhitespace(in);
  end
endmodule
module trim_ws_mod(input string in, output string out);
  always_comb begin
    out = VString_trimWhitespace(in);
  end
endmodule
module is_id_mod(input string in, output logic ok);
  always_comb begin
    ok = VString_isIdentifier(in);
  end
endmodule
module is_ws_mod(input string in, output logic ok);
  always_comb begin
    ok = VString_isWhitespace(in);
  end
endmodule
module leading_ws_count_mod(input string in, output int count);
  always_comb begin
    count = VString_leadingWhitespaceCount(in);
  end
endmodule
module parse_double_mod(input string in, output real value, output logic success);
  always_comb begin
    value = VString_parseDouble(in, success);
  end
endmodule
module replace_substr_mod(input string s, input string from, input string to, output string out);
  always_comb begin
    out = VString_replaceSubstr(s, from, to);
  end
endmodule
module replace_word_mod(input string s, input string from, input string to, output string out);
  always_comb begin
    out = VString_replaceWord(s, from, to);
  end
endmodule
module starts_with_mod(input string s, input string pref, output logic ok);
  always_comb begin
    ok = VString_startsWith(s, pref);
  end
endmodule
module ends_with_mod(input string s, input string suf, output logic ok);
  always_comb begin
    ok = VString_endsWith(s, suf);
  end
endmodule
module a_or_an_mod(input string w, output string art);
  always_comb begin
    art = VString_aOrAn(w);
  end
endmodule
module hash_murmur_mod(input string s, output longint h);
  always_comb begin
    h = VString_hashMurmur(s);
  end
endmodule
module vname_dehash_mod(input string in, output string out);
  always_comb begin
    out = VName_dehash(in);
  end
endmodule
module vname_hashed_mod(input bit en, output string out);
  always_comb begin
    out = VName_hashedName();
  end
endmodule
module sha256_hex_mod(input bit en, output string hexout);
  always_comb begin
    hexout = VHashSha256_digestHex();
  end
endmodule
module sha256_sym_mod(input bit en, output string symout);
  always_comb begin
    symout = VHashSha256_digestSymbol();
  end
endmodule
module spell_edit_mod(input string a, input string b, output int dist_out);
  always_comb begin
    dist_out = VSpellCheck_editDistance(a, b);
  end
endmodule
module spell_cutoff_mod(input int g, input int c, output int dist_out);
  always_comb begin
    dist_out = VSpellCheck_cutoffDistance(g, c);
  end
endmodule
module spell_best_mod(input string goal, output string best_out, output int dist_out);
  always_comb begin
    best_out = VSpellCheck_bestCandidateInfo(goal, dist_out);
  end
endmodule
