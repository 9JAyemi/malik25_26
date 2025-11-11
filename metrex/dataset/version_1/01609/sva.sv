// SVA for adder
module adder_sva (
  input logic        clk,
  input logic [7:0]  A, B, S,
  input logic [7:0]  S_reg
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity: no X on inputs
  ap_inputs_known: assert property (!$isunknown(A) && !$isunknown(B));

  // Functional check: 1-cycle registered sum (modulo 256)
  ap_sum_correct: assert property (
    disable iff ($isunknown($past(A)) || $isunknown($past(B)))
    S == $past(A) + $past(B)
  );

  // Structural check: output matches internal register
  ap_out_matches_reg: assert property (
    disable iff ($isunknown(S) || $isunknown(S_reg))
    S == S_reg
  );

  // Coverage: exercise no-carry and carry cases
  cp_no_carry: cover property (
    disable iff ($isunknown($past(A)) || $isunknown($past(B)))
    !(({1'b0,$past(A)} + {1'b0,$past(B)})[8])
  );

  cp_with_carry: cover property (
    disable iff ($isunknown($past(A)) || $isunknown($past(B)))
    ({1'b0,$past(A)} + {1'b0,$past(B)})[8]
  );

  // Coverage: notable result values and edges
  cp_sum_zero: cover property (
    disable iff ($isunknown($past(A)) || $isunknown($past(B)))
    S == 8'h00
  );

  cp_sum_ff: cover property (
    disable iff ($isunknown($past(A)) || $isunknown($past(B)))
    S == 8'hFF
  );

  cp_wrap_example: cover property (
    disable iff ($isunknown($past(A)) || $isunknown($past(B)))
    ($past(A) == 8'hFF && $past(B) == 8'h01 && S == 8'h00)
  );
endmodule

// Bind into DUT
bind adder adder_sva sva_i(.clk(clk), .A(A), .B(B), .S(S), .S_reg(S_reg));