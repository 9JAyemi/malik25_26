// SVA for sky130_fd_sc_ms__nor3

module sky130_fd_sc_ms__nor3_sva (
  input logic A, B, C,
  input logic Y,
  input logic nor0_out_Y
);

  // Functional correctness when inputs are known
  property p_func_known;
    @(A or B or C or Y)
      !$isunknown({A,B,C}) |-> (Y === ~(A|B|C));
  endproperty
  a_func_known: assert property (p_func_known);

  // Dominating 1 forces output low (even with X/Z on others)
  a_any1_forces0: assert property (@(A or B or C or Y)
    (A===1 || B===1 || C===1) |-> (Y===1'b0));

  // All-zero forces output high
  a_all0_forces1: assert property (@(A or B or C or Y)
    (A===0 && B===0 && C===0) |-> (Y===1'b1));

  // X/Z propagation when no input is 1
  a_x_prop_when_no1: assert property (@(A or B or C or Y)
    (!(A===1||B===1||C===1) && $isunknown({A,B,C})) |-> $isunknown(Y));

  // Output should never be Z
  a_no_Z: assert property (@(A or B or C or Y) (Y !== 1'bz));

  // Buffer integrity: Y mirrors nor0_out_Y
  a_buf_integrity: assert property (@(A or B or C or Y) (Y === nor0_out_Y));

  // Full functional coverage of all known input combinations
  c_000: cover property (@(A or B or C or Y) (A===0 && B===0 && C===0 && Y===1));
  c_001: cover property (@(A or B or C or Y) (A===0 && B===0 && C===1 && Y===0));
  c_010: cover property (@(A or B or C or Y) (A===0 && B===1 && C===0 && Y===0));
  c_100: cover property (@(A or B or C or Y) (A===1 && B===0 && C===0 && Y===0));
  c_011: cover property (@(A or B or C or Y) (A===0 && B===1 && C===1 && Y===0));
  c_101: cover property (@(A or B or C or Y) (A===1 && B===0 && C===1 && Y===0));
  c_110: cover property (@(A or B or C or Y) (A===1 && B===1 && C===0 && Y===0));
  c_111: cover property (@(A or B or C or Y) (A===1 && B===1 && C===1 && Y===0));

  // X-behavior coverage: dominance and propagation
  c_any1_dominates_x: cover property (@(A or B or C or Y)
    ((A===1 || B===1 || C===1) && $isunknown({A,B,C}) && Y===0));
  c_x_propagates_no1: cover property (@(A or B or C or Y)
    (!(A===1||B===1||C===1) && $isunknown({A,B,C}) && $isunknown(Y)));

endmodule

bind sky130_fd_sc_ms__nor3 sky130_fd_sc_ms__nor3_sva sva_bind (
  .A(A), .B(B), .C(C), .Y(Y), .nor0_out_Y(nor0_out_Y)
);