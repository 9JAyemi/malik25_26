// SVA/checkers for dectohexstr24 and dectohexstr8
package dectohexstr_sva_pkg;
  function automatic byte nib2asc (bit [3:0] n);
    case (n)
      4'h0: return "0"; 4'h1: return "1"; 4'h2: return "2"; 4'h3: return "3";
      4'h4: return "4"; 4'h5: return "5"; 4'h6: return "6"; 4'h7: return "7";
      4'h8: return "8"; 4'h9: return "9"; 4'hA: return "A"; 4'hB: return "B";
      4'hC: return "C"; 4'hD: return "D"; 4'hE: return "E"; default: return "F";
    endcase
  endfunction

  function automatic bit is_hex_char (byte c);
    return ((c >= "0" && c <= "9") || (c >= "A" && c <= "F"));
  endfunction
endpackage

// Checker for leaf module dectohexstr8
module dectohexstr8_sva(input logic [7:0] in, input logic [15:0] out);
  import dectohexstr_sva_pkg::*;

  // Combinational correctness and X/Z checks
  always_comb begin
    assert (!$isunknown({in,out})) else $error("dectohexstr8: X/Z on I/O");
    assert (out[7:0]  == nib2asc(in[3:0]))  else $error("dectohexstr8: low nibble ASCII mismatch");
    assert (out[15:8] == nib2asc(in[7:4]))  else $error("dectohexstr8: high nibble ASCII mismatch");
    assert (is_hex_char(out[7:0]) && is_hex_char(out[15:8]))
      else $error("dectohexstr8: non-hex ASCII output");
  end

  // Functional coverage: exercise all nibble values on both nibbles
  covergroup cg_nibs @(in);
    coverpoint in[3:0]  { bins all[] = {[0:15]}; }
    coverpoint in[7:4]  { bins all[] = {[0:15]}; }
  endgroup
  cg_nibs cg = new();
endmodule

// Checker for top module dectohexstr24
module dectohexstr24_sva(input logic [23:0] in, input logic [127:0] out);
  import dectohexstr_sva_pkg::*;

  // Combinational correctness and X/Z checks
  always_comb begin
    assert (!$isunknown({in,out})) else $error("dectohexstr24: X/Z on I/O");

    // Left padding must be exactly 10 spaces
    assert (out[127:48] == "          ") else $error("dectohexstr24: padding not 10 spaces");

    // Per-byte hex ASCII mapping (LSB byte first)
    assert (out[7:0]   == nib2asc(in[3:0]))    else $error("dectohexstr24: [7:0] char mismatch");
    assert (out[15:8]  == nib2asc(in[7:4]))    else $error("dectohexstr24: [15:8] char mismatch");

    assert (out[23:16] == nib2asc(in[11:8]))   else $error("dectohexstr24: [23:16] char mismatch");
    assert (out[31:24] == nib2asc(in[15:12]))  else $error("dectohexstr24: [31:24] char mismatch");

    assert (out[39:32] == nib2asc(in[19:16]))  else $error("dectohexstr24: [39:32] char mismatch");
    assert (out[47:40] == nib2asc(in[23:20]))  else $error("dectohexstr24: [47:40] char mismatch");

    // Ensure all 6 emitted characters are valid hex ASCII
    assert (is_hex_char(out[7:0])   && is_hex_char(out[15:8]) &&
            is_hex_char(out[23:16]) && is_hex_char(out[31:24]) &&
            is_hex_char(out[39:32]) && is_hex_char(out[47:40]))
      else $error("dectohexstr24: non-hex ASCII character in output");
  end

  // Functional coverage: all nibble values seen across entire 24b input
  covergroup cg_nibs24 @(in);
    coverpoint in[3:0]    { bins all[] = {[0:15]}; }
    coverpoint in[7:4]    { bins all[] = {[0:15]}; }
    coverpoint in[11:8]   { bins all[] = {[0:15]}; }
    coverpoint in[15:12]  { bins all[] = {[0:15]}; }
    coverpoint in[19:16]  { bins all[] = {[0:15]}; }
    coverpoint in[23:20]  { bins all[] = {[0:15]}; }
  endgroup
  cg_nibs24 cg = new();

  // Sanity pattern coverage (optional but useful)
  cover property (in == 24'h000000);
  cover property (in == 24'hFFFFFF);
  cover property (in == 24'h123456);
  cover property (in == 24'hABCDEF);
endmodule

// Bind checkers to DUTs
bind dectohexstr8  dectohexstr8_sva  dectohexstr8_sva_i (.in(in), .out(out));
bind dectohexstr24 dectohexstr24_sva dectohexstr24_sva_i (.in(in), .out(out));