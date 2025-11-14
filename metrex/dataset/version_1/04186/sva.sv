// Bindable SVA for dffsr
module dffsr_sva (
  input logic CLK,
  input logic D,
  input logic R,
  input logic S,
  input logic Q
);

  default clocking cb @(posedge CLK); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge CLK) past_valid <= 1;

  // Basic sanity of inputs/outputs
  assert property (!$isunknown({R,S,D})) else $error("dffsr: X/Z on inputs at clk");
  assert property (past_valid |-> !$isunknown(Q)) else $error("dffsr: Q is X/Z after an update");

  // Functional spec: synchronous reset/set with priority R > S, else load D
  assert property (
    past_valid |-> Q == ($past(R) ? 1'b0 :
                         $past(S) ? 1'b1 :
                                    $past(D))
  ) else $error("dffsr: Q functional mismatch");

  // Explicit priority check when R and S both asserted
  assert property (past_valid && $past(R && S) |-> Q == 1'b0)
    else $error("dffsr: R/S priority violated (Q must be 0)");

  // Coverage: exercise all branches
  cover property (past_valid && $past(R) && Q == 1'b0);                           // reset branch
  cover property (past_valid && !$past(R) && $past(S) && Q == 1'b1);              // set branch
  cover property (past_valid && !$past(R) && !$past(S) && Q == $past(D));         // load branch
  cover property (past_valid && $past(R && S) && Q == 1'b0);                      // simultaneous R&S

  // Coverage: load path toggles both ways
  cover property (past_valid && !$past(R|S) && $past(Q)==1'b0 && $past(D)==1'b1 && Q==1'b1);
  cover property (past_valid && !$past(R|S) && $past(Q)==1'b1 && $past(D)==1'b0 && Q==1'b0);

endmodule

// Bind into the DUT
bind dffsr dffsr_sva sva_inst (.*);