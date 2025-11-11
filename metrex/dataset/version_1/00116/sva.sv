// SVA for sky130_fd_sc_ls__nor4
// Bind this module to the DUT to check correctness and collect coverage.

module sky130_fd_sc_ls__nor4_sva (
  input logic A, B, C, D,
  input logic Y
);

  // Core functional correctness (known inputs)
  property p_func_known;
    @(A or B or C or D or Y)
      !$isunknown({A,B,C,D}) |-> (Y === ~(A|B|C|D));
  endproperty
  assert property (p_func_known);

  // Strong X-prop/4-state correctness
  // If any input is 1, output must be 0 (even with X/Z on others)
  assert property (@(A or B or C or D or Y)
                   ((A===1'b1)||(B===1'b1)||(C===1'b1)||(D===1'b1)) |-> (Y===1'b0));

  // If all inputs are 0, output must be 1
  assert property (@(A or B or C or D or Y)
                   ((A===1'b0)&&(B===1'b0)&&(C===1'b0)&&(D===1'b0)) |-> (Y===1'b1));

  // If no inputs are 1 and at least one is X/Z, output must be X
  assert property (@(A or B or C or D or Y)
                   (!(A===1||B===1||C===1||D===1) && $isunknown({A,B,C,D})) |-> (Y===1'bx));

  // Output should never be high-Z
  assert property (@(Y) Y !== 1'bz);

  // No spurious output change: Y changes only if NOR-of-inputs changes
  assert property (@(A or B or C or D or Y)
                   $changed(Y) |-> $changed(~(A|B|C|D)));

  // Functional coverage: all 16 input combinations observed
  cover property (@(A or B or C or D) ({A,B,C,D} === 4'b0000));
  cover property (@(A or B or C or D) ({A,B,C,D} === 4'b0001));
  cover property (@(A or B or C or D) ({A,B,C,D} === 4'b0010));
  cover property (@(A or B or C or D) ({A,B,C,D} === 4'b0011));
  cover property (@(A or B or C or D) ({A,B,C,D} === 4'b0100));
  cover property (@(A or B or C or D) ({A,B,C,D} === 4'b0101));
  cover property (@(A or B or C or D) ({A,B,C,D} === 4'b0110));
  cover property (@(A or B or C or D) ({A,B,C,D} === 4'b0111));
  cover property (@(A or B or C or D) ({A,B,C,D} === 4'b1000));
  cover property (@(A or B or C or D) ({A,B,C,D} === 4'b1001));
  cover property (@(A or B or C or D) ({A,B,C,D} === 4'b1010));
  cover property (@(A or B or C or D) ({A,B,C,D} === 4'b1011));
  cover property (@(A or B or C or D) ({A,B,C,D} === 4'b1100));
  cover property (@(A or B or C or D) ({A,B,C,D} === 4'b1101));
  cover property (@(A or B or C or D) ({A,B,C,D} === 4'b1110));
  cover property (@(A or B or C or D) ({A,B,C,D} === 4'b1111));

  // Coverage for X/Z on inputs and X on output (X-prop scenario)
  cover property (@(A or B or C or D) $isunknown({A,B,C,D}));
  cover property (@(A or B or C or D) (!(A===1||B===1||C===1||D===1) && $isunknown({A,B,C,D}) && (Y===1'bx)));

  // Output toggle coverage
  cover property (@(posedge Y) 1);
  cover property (@(negedge Y) 1);

endmodule

// Bind to all instances of the DUT
bind sky130_fd_sc_ls__nor4 sky130_fd_sc_ls__nor4_sva nor4_sva_i (.A(A), .B(B), .C(C), .D(D), .Y(Y));