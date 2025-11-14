// SVA for up_down_counter
// Bind this module to the DUT: bind up_down_counter up_down_counter_sva sva(.CLK, .UD, .Q);

module up_down_counter_sva (input CLK, input UD, input [3:0] Q);
  default clocking cb @(posedge CLK); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge CLK) past_valid <= 1'b1;

  // Basic sanity: no X/Z after first sampled cycle
  assert property (past_valid |-> !$isunknown(Q)) else $error("Q is X/Z");
  assert property (past_valid |-> !$isunknown($past(UD))) else $error("UD was X/Z when sampled");

  // Core functional spec (mod-16 up/down by 1, including wrap)
  // Delta modulo-16 equals +1 when UD=0, -1 (i.e. 0xF) when UD=1
  assert property (past_valid |-> ( (Q - $past(Q)) == ($past(UD) ? 4'hF : 4'h1) ))
    else $error("Counter step mismatch");

  // Useful covers
  cover property (past_valid && ($past(UD)==1'b0) && ($past(Q)==4'hF) && (Q==4'h0)); // up wrap 15->0
  cover property (past_valid && ($past(UD)==1'b1) && ($past(Q)==4'h0) && (Q==4'hF)); // down wrap 0->15
  cover property (past_valid && $changed(UD)); // direction toggle observed
endmodule

// Example bind (place in a testbench or a separate bind file):
// bind up_down_counter up_down_counter_sva sva(.CLK(CLK), .UD(UD), .Q(Q));