// SVA for sky130_fd_sc_hd__o221ai: Y = ~((A1|A2) & (B1|B2) & C1)

module sky130_fd_sc_hd__o221ai_sva (
  input logic A1, A2, B1, B2, C1, Y
);
  logic grpA, grpB;
  assign grpA = (A1 | A2);
  assign grpB = (B1 | B2);

  // Sample on any relevant change; use ##0 to avoid race with combinational settle
  `define O221AI_EVT (A1 or A2 or B1 or B2 or C1 or Y)

  // Functional equivalence (4-state accurate)
  property p_func;
    @(`O221AI_EVT) 1'b1 |-> ##0 ( Y === ~(grpA & grpB & C1) );
  endproperty
  assert property (p_func);

  // Only way to get Y=0 is all three terms =1
  property p_y0_only_when_all_true;
    @(`O221AI_EVT) (Y===1'b0) |-> ##0 (C1===1'b1 && grpA===1'b1 && grpB===1'b1);
  endproperty
  assert property (p_y0_only_when_all_true);

  // Controlling-0s force Y=1 (X-safe)
  property p_c1_zero_forces_one;
    @(`O221AI_EVT) (C1===1'b0) |-> ##0 (Y===1'b1);
  endproperty
  assert property (p_c1_zero_forces_one);

  property p_agrp_zero_forces_one;
    @(`O221AI_EVT) ((A1===1'b0)&&(A2===1'b0)) |-> ##0 (Y===1'b1);
  endproperty
  assert property (p_agrp_zero_forces_one);

  property p_bgrp_zero_forces_one;
    @(`O221AI_EVT) ((B1===1'b0)&&(B2===1'b0)) |-> ##0 (Y===1'b1);
  endproperty
  assert property (p_bgrp_zero_forces_one);

  // If inputs are known 0/1, output must be known 0/1
  property p_no_x_when_inputs_known;
    @(`O221AI_EVT) (!$isunknown({A1,A2,B1,B2,C1})) |-> ##0 (!$isunknown(Y));
  endproperty
  assert property (p_no_x_when_inputs_known);

  // Coverage: both output values and each independent controlling path
  cover property (@(`O221AI_EVT) ##0 (C1===1'b1 && grpA===1'b1 && grpB===1'b1 && Y===1'b0)); // Y=0 case
  cover property (@(`O221AI_EVT) ##0 (C1===1'b0 && grpA===1'b1 && grpB===1'b1 && Y===1'b1)); // forced by C1=0
  cover property (@(`O221AI_EVT) ##0 (C1===1'b1 && grpA===1'b0 && grpB===1'b1 && Y===1'b1)); // forced by A-group=0
  cover property (@(`O221AI_EVT) ##0 (C1===1'b1 && grpA===1'b1 && grpB===1'b0 && Y===1'b1)); // forced by B-group=0
  cover property (@(`O221AI_EVT) $rose(Y));
  cover property (@(`O221AI_EVT) $fell(Y));
endmodule

// Bind into the DUT
bind sky130_fd_sc_hd__o221ai sky130_fd_sc_hd__o221ai_sva o221ai_sva_i (.*);