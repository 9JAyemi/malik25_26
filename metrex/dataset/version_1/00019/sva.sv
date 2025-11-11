// SVA for the simple combinational design (clockless, concise, quality-focused)
// Bind these into the DUT. Assertions are concurrent (clockless) and include minimal coverage.

`ifndef SYNTHESIS

// AND gate assertions
module and_gate_sva(input logic a,b,c,d, input logic out);
  // Functional equivalence
  assert property (out == (a & b & c & d))
    else $error("%m and_gate: out != a&b&c&d");

  // Basic coverage
  cover property (out == 1'b0);
  cover property (out == 1'b1);
endmodule

// OR gate assertions
module or_gate_sva(input logic a,b,c,d, input logic out);
  assert property (out == (a | b | c | d))
    else $error("%m or_gate: out != a|b|c|d");

  cover property (out == 1'b0);
  cover property (out == 1'b1);
endmodule

// XOR gate assertions
module xor_gate_sva(input logic a,b, input logic out);
  assert property (out == (a ^ b))
    else $error("%m xor_gate: out != a^b");

  cover property (out == 1'b0);
  cover property (out == 1'b1);
  cover property ($changed(out));
endmodule

// Combined module assertions (also checks internal nets)
module combined_module_sva(
  input logic [3:0] in,
  input logic       out,
  input logic       and_out,
  input logic       or_out
);
  // Internal gate correctness
  assert property (and_out == (&in))
    else $error("%m combined: and_out != &in");
  assert property (or_out  == (|in))
    else $error("%m combined: or_out != |in");

  // Top-level function
  assert property (out == (and_out ^ or_out))
    else $error("%m combined: out != and_out ^ or_out");

  // Logical consistency: when all bits are 1, OR must be 1; if AND is 1 then OR must be 1
  assert property (and_out |-> or_out)
    else $error("%m combined: and_out implies or_out violated");

  // Minimal but meaningful coverage
  cover property (in == 4'h0); // all zeros
  cover property (in == 4'hF); // all ones
  cover property ($changed(out));

  // Full input-space coverage of 4-bit in (16 combos)
  genvar i;
  for (i = 0; i < 16; i++) begin : COV_ALL_IN
    localparam logic [3:0] VAL = i[3:0];
    cover property (in == VAL);
  end
endmodule

// Optional top-level equivalence assertion (redundant but catches binding issues)
module top_module_sva(input logic [3:0] in, input logic out);
  assert property (out == ((&in) ^ (|in)))
    else $error("%m top: out != (&in) ^ (|in)");
  cover property ($changed(out));
endmodule

// Binds
bind and_gate        and_gate_sva        and_gate_sva_i       (.a(a), .b(b), .c(c), .d(d), .out(out));
bind or_gate         or_gate_sva         or_gate_sva_i        (.a(a), .b(b), .c(c), .d(d), .out(out));
bind xor_gate        xor_gate_sva        xor_gate_sva_i       (.a(a), .b(b),             .out(out));
bind combined_module combined_module_sva combined_module_sva_i(.in(in), .out(out), .and_out(and_out), .or_out(or_out));
bind top_module      top_module_sva      top_module_sva_i     (.in(in), .out(out));

`endif // SYNTHESIS