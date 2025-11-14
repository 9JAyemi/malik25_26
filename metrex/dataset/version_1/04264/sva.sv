// SVA for eight_bit_comparator
// Concise checks for stage sequencing, comparator correctness, one-hot outputs, and coverage.

module eight_bit_comparator_sva (
  input  logic        clk,
  input  logic [7:0]  A,
  input  logic [7:0]  B,
  input  logic        equal,
  input  logic        A_greater_than_B,
  input  logic        A_less_than_B,
  input  logic [2:0]  stage
);

  default clocking cb @(posedge clk); endclocking

  function automatic logic [7:0] eff_shift (input logic [7:0] x, input logic [2:0] s);
    case (s)
      3'd0: eff_shift = x;
      3'd1: eff_shift = x >> 1;
      3'd2: eff_shift = x >> 2;
      3'd3: eff_shift = x >> 4;
      default: eff_shift = 'x;
    endcase
  endfunction

  // Stage must stay within 0..3 and step 0->1->2->3->0
  a_stage_in_range: assert property (disable iff ($isunknown(stage)) stage inside {[0:3]});
  a_stage_step0:    assert property ( !$isunknown($past(stage)) && $past(stage)==3'd0 |-> stage==3'd1 );
  a_stage_step1:    assert property ( !$isunknown($past(stage)) && $past(stage)==3'd1 |-> stage==3'd2 );
  a_stage_step2:    assert property ( !$isunknown($past(stage)) && $past(stage)==3'd2 |-> stage==3'd3 );
  a_stage_step3:    assert property ( !$isunknown($past(stage)) && $past(stage)==3'd3 |-> stage==3'd0 );

  // When inputs and stage are known and legal, outputs must be known and correct vs shifted inputs
  a_outputs_known: assert property (
    stage inside {[0:3]} && !$isunknown({A,B}) |-> !$isunknown({equal,A_greater_than_B,A_less_than_B})
  );

  a_compare_correct: assert property (
    stage inside {[0:3]} && !$isunknown({A,B}) |->
      ( equal              === (eff_shift(A,stage) == eff_shift(B,stage)) &&
        A_greater_than_B   === (eff_shift(A,stage) >  eff_shift(B,stage)) &&
        A_less_than_B      === (eff_shift(A,stage) <  eff_shift(B,stage)) )
  );

  // One-hot check on outputs when known
  a_onehot_outputs: assert property (
    !$isunknown({equal,A_greater_than_B,A_less_than_B}) |-> $onehot({equal,A_greater_than_B,A_less_than_B})
  );

  // Coverage: stage cycling and each outcome at each stage
  c_stage_cycle: cover property (stage==0 ##1 stage==1 ##1 stage==2 ##1 stage==3 ##1 stage==0);

  genvar s;
  generate
    for (s=0; s<4; s++) begin : C_PER_STAGE
      c_eq:  cover property (stage==s && equal);
      c_gt:  cover property (stage==s && A_greater_than_B);
      c_lt:  cover property (stage==s && A_less_than_B);
    end
  endgenerate

  // Boundary value coverage (some useful points)
  c_eq_zero:   cover property (stage==0 && A==8'h00 && B==8'h00 && equal);
  c_eq_ff:     cover property (stage==0 && A==8'hFF && B==8'hFF && equal);
  c_gt_edge:   cover property (stage==0 && A==8'h80 && B==8'h7F && A_greater_than_B);
  c_lt_edge:   cover property (stage==0 && A==8'h7F && B==8'h80 && A_less_than_B);

endmodule

// Bind SVA to the DUT
bind eight_bit_comparator eight_bit_comparator_sva sva_i (
  .clk(clk),
  .A(A),
  .B(B),
  .equal(equal),
  .A_greater_than_B(A_greater_than_B),
  .A_less_than_B(A_less_than_B),
  .stage(stage)
);