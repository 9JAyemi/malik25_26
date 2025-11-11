// SVA checker for AND_GATE
module AND_GATE_sva(input logic a, b, y);

  // Functional correctness (4-state accurate), sampled after updates
  property p_and_truth;
    @(a or b or y) 1 |-> ##0 (y === (a & b));
  endproperty
  A_AND_TRUTH: assert property (p_and_truth);

  // If inputs are known, output must be known
  property p_y_known_if_inputs_known;
    @(a or b or y) ((a !== 1'bx && b !== 1'bx) |-> ##0 (y !== 1'bx));
  endproperty
  A_Y_KNOWN: assert property (p_y_known_if_inputs_known);

  // Functional coverage: all input/output combinations
  C_00: cover property (@(a or b or y) ##0 (a==0 && b==0 && y==0));
  C_01: cover property (@(a or b or y) ##0 (a==0 && b==1 && y==0));
  C_10: cover property (@(a or b or y) ##0 (a==1 && b==0 && y==0));
  C_11: cover property (@(a or b or y) ##0 (a==1 && b==1 && y==1));

  // Coverage: key transitions driving y
  C_RISE_A: cover property (@(posedge a) (b===1) ##0 (y===1));
  C_RISE_B: cover property (@(posedge b) (a===1) ##0 (y===1));
  C_FALL_A: cover property (@(negedge a) (b===1) ##0 (y===0));
  C_FALL_B: cover property (@(negedge b) (a===1) ##0 (y===0));

  // X-propagation coverage
  C_AX_B1: cover property (@(a or b or y) (a===1'bx && b===1) ##0 (y===1'bx));
  C_AX_B0: cover property (@(a or b or y) (a===1'bx && b===0) ##0 (y===0));
  C_BX_A1: cover property (@(a or b or y) (b===1'bx && a===1) ##0 (y===1'bx));
  C_BX_A0: cover property (@(a or b or y) (b===1'bx && a===0) ##0 (y===0));

endmodule

// Bind into the DUT
bind AND_GATE AND_GATE_sva sva_and (.a(a), .b(b), .y(y));