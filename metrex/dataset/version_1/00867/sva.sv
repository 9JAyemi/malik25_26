// SVA for d_flip_flop
module d_flip_flop_sva (input logic CK, D, RST, Q, QN);

  // Sample on clock edges that can change outputs
  default clocking cb @(posedge CK or negedge RST); endclocking
  // Ignore checks while RST is X/Z
  default disable iff ($isunknown(RST));

  // 1) Asynchronous reset drives values immediately
  assert property ($fell(RST) |-> ##0 (Q==1'b0 && QN==1'b1));

  // 2) While in reset, outputs hold reset values
  assert property (!RST |-> (Q==1'b0 && QN==1'b1));

  // 3) Functional capture on clock when not in reset
  assert property (@(posedge CK) RST |-> (Q==$past(D) && QN==~$past(D)));

  // 4) Outputs are always complementary at update points
  assert property (QN == ~Q);

  // 5) No X/Z on outputs at update points
  assert property (!$isunknown({Q,QN}));

  // Optional stability check during reset (concise form)
  assert property (@(posedge CK) !RST |-> $stable({Q,QN}));

  // Coverage
  cover property ($fell(RST));                                // reset asserted
  cover property (@(posedge CK) $past(!RST) && RST);          // reset released then first clk
  cover property (@(posedge CK) RST && $past(D)==1 && Q==1);  // capture 1
  cover property (@(posedge CK) RST && $past(D)==0 && Q==0);  // capture 0
  cover property (@(posedge CK) RST && $changed(Q));          // Q toggled in run mode

endmodule

// Bind to DUT
bind d_flip_flop d_flip_flop_sva sva_i (.*);