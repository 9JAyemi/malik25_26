// SVA for the given design. Focused, concise, and bind-based.
// Place this in a separate file and compile with the DUT.

package top_sva_pkg;
  function automatic [3:0] rotl4(input [3:0] x);
    rotl4 = {x[2:0], x[3]};
  endfunction
endpackage

// ---------------- full_adder ----------------
module full_adder_sva;
  default clocking cb @(*); endclocking

  // No X/Z on inputs/outputs
  assert property (!$isunknown({a, b, cin, sum, cout}));

  // Functional equivalence
  assert property (sum == (a ^ b ^ cin));
  assert property (cout == ((a & b) | (a & cin) | (b & cin)));

  // Carry generation coverage
  cover property ( (a & b) || (a & cin) || (b & cin) );
endmodule
bind full_adder full_adder_sva fa_sva();

// ---------------- four_bit_adder ----------------
module four_bit_adder_sva;
  default clocking cb @(*); endclocking

  import top_sva_pkg::*;

  // No X/Z on key signals
  assert property (!$isunknown({a, b, sum, c1, c2, c3}));

  // Ripple-carry bit-level checks
  assert property (c1 == (a[0] & b[0]));
  assert property (c2 == ((a[1] & b[1]) | (a[1] & c1) | (b[1] & c1)));
  assert property (c3 == ((a[2] & b[2]) | (a[2] & c2) | (b[2] & c2)));

  // Sum equivalences
  assert property (sum == (a ^ b ^ {c3, c2, c1, 1'b0}));
  assert property (sum == (a + b)[3:0]);

  // Overflow (carry-out of MSB) coverage
  cover property ( (a + b)[4] );
endmodule
bind four_bit_adder four_bit_adder_sva fba_sva();

// ---------------- shift_register ----------------
module shift_register_sva;
  default clocking cb @(*); endclocking
  import top_sva_pkg::*;

  // No X/Z on interface
  assert property (!$isunknown({data_in, shift_output}));

  // After NBA delta, output equals rotate-left by 1 of data_in
  assert property (1'b1 |-> ##0 (shift_output == rotl4(data_in)));

  // Stability: if input stable, output stable
  assert property ($stable(data_in) |-> $stable(shift_output));

  // Coverage: classic rotate of 1000 -> 0001
  cover property ( (data_in == 4'b1000) ##0 (shift_output == 4'b0001) );
endmodule
bind shift_register shift_register_sva sr_sva();

// ---------------- xor_output ----------------
module xor_output_sva;
  default clocking cb @(*); endclocking

  // No X/Z on interface
  assert property (!$isunknown({shift_data, b, out}));

  // Functional XOR (after delta for propagation)
  assert property (1'b1 |-> ##0 (out == (shift_data ^ b)));

  // Coverage: extremes
  cover property (out == 4'h0);
  cover property (out == 4'hF);
endmodule
bind xor_output xor_output_sva xo_sva();

// ---------------- top_module (end-to-end) ----------------
module top_module_sva;
  default clocking cb @(*); endclocking
  import top_sva_pkg::*;

  // No X/Z on primary I/O and key internal nets
  assert property (!$isunknown({a, b, adder_output, shift_output, out}));

  // Block-level composition checks (include ##0 for NBA in shift_reg)
  assert property (1'b1 |-> ##0 (adder_output == (a + b)[3:0]));
  assert property (1'b1 |-> ##0 (shift_output == rotl4(adder_output)));
  assert property (1'b1 |-> ##0 (out == (shift_output ^ b)));

  // End-to-end functional check
  assert property (1'b1 |-> ##0 (out == (rotl4((a + b)[3:0]) ^ b)));

  // Useful coverage
  cover property ( (a + b)[4] );        // adder overflow
  cover property ( $onehot(adder_output) );
  cover property ( out == 4'h0 );
endmodule
bind top_module top_module_sva top_sva();