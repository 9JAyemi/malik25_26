// SVA checker for top_module
module top_module_sva (
  input  [7:0]  in0, in1, in2, in3,
  input  [1:0]  sel,
  input  [15:0] out_not,
  input  [7:0]  out_and_bitwise,
  input  [7:0]  out_xor_bitwise,
  input  [7:0]  out_nor_bitwise
);

  // Sample on any input/output change (combinational design)
  default clocking cb @(in0 or in1 or in2 or in3 or sel
                        or out_not or out_and_bitwise or out_xor_bitwise or out_nor_bitwise); endclocking

  // Core functional correctness
  ap_and:  assert property (out_and_bitwise == (in0 & in1));
  ap_xor:  assert property (out_xor_bitwise == (in2 ^ in3));
  ap_nor:  assert property (out_nor_bitwise == ~(in0 | in1));

  // Mux + invert behavior on out_not lower byte
  ap_not_lo: assert property (
    out_not[7:0] ==
      ~((sel==2'b00) ? in0 :
        (sel==2'b01) ? in1 :
        (sel==2'b10) ? in2 : in3)
  );

  // Upper byte only depends on in2 due to width truncation in DUT (~{in3,in2} -> lower 8 bits)
  ap_not_hi: assert property (out_not[15:8] == ~in2);

  // Algebraic consistency between AND and NOR of same operands
  ap_and_nor_disjoint: assert property ( (out_and_bitwise & out_nor_bitwise) == 8'h00 );
  ap_and_nor_cover_xnor: assert property ( (out_and_bitwise | out_nor_bitwise) == ~(in0 ^ in1) );

  // No X/Z on outputs when inputs are known
  ap_no_x_prop: assert property (
    !$isunknown({in0,in1,in2,in3,sel}) |-> !$isunknown({out_not,out_and_bitwise,out_xor_bitwise,out_nor_bitwise})
  );

  // Minimal but meaningful coverage
  // Each mux selection observed with correct lower-byte inversion
  cp_sel_00: cover property (sel==2'b00 && out_not[7:0]==~in0);
  cp_sel_01: cover property (sel==2'b01 && out_not[7:0]==~in1);
  cp_sel_10: cover property (sel==2'b10 && out_not[7:0]==~in2);
  cp_sel_11: cover property (sel==2'b11 && out_not[7:0]==~in3);

  // Extremes for bitwise results to ensure good stimulus
  cp_and_all0:  cover property (out_and_bitwise == 8'h00);
  cp_and_all1:  cover property (out_and_bitwise == 8'hFF);
  cp_xor_all0:  cover property (out_xor_bitwise == 8'h00);
  cp_xor_all1:  cover property (out_xor_bitwise == 8'hFF);
  cp_nor_all0:  cover property (out_nor_bitwise == 8'h00);
  cp_nor_all1:  cover property (out_nor_bitwise == 8'hFF);

  // Highlight that in3 does not influence upper byte of out_not (intent check)
  cp_in3_ignored_hi: cover property ($changed(in3) && $stable(in2) && $stable(out_not[15:8]));

endmodule

// Bind into the DUT (if desired)
// bind top_module top_module_sva sva_inst(.*);