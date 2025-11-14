// SVA for three_input_gate
module three_input_gate_sva (
  input logic clk,
  input logic A1,
  input logic A2,
  input logic B1,
  input logic Y
);

  default clocking cb @(posedge clk); endclocking

  // Golden next-state function (per RTL if/else chain)
  function automatic logic exp_y (input logic A1i, A2i, B1i);
    exp_y = (A1i && A2i) ? 1'b0
         : (!A1i && A2i) ? 1'b1
         : (A1i && !A2i) ? B1i
         :                  1'b1;
  endfunction

  // Core functional check: Y(t) equals function of inputs at t-1
  assert property (1'b1 |=> (Y == exp_y($past(A1), $past(A2), $past(B1))))
    else $error("Y mismatch vs spec");

  // Basic sanity: Y is never X/Z after the first update
  assert property (1'b1 |=> !$isunknown(Y))
    else $error("Y is unknown");

  // Functional coverage: exercise all input cases and B1 gating
  cover property ((A1 && A2)        |=> (Y == 1'b0));
  cover property ((!A1 && A2)       |=> (Y == 1'b1));
  cover property ((A1 && !A2 && !B1)|=> (Y == 1'b0));
  cover property ((A1 && !A2 &&  B1)|=> (Y == 1'b1));
  cover property ((!A1 && !A2)      |=> (Y == 1'b1));

endmodule

bind three_input_gate three_input_gate_sva sva_i (.*);