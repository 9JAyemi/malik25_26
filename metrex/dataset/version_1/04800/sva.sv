// SVA checker for dff: checks 1-cycle capture semantics, X-propagation, and change consistency.
module dff_sva(input logic D, CLK, Q);

  default clocking cb @(posedge CLK); endclocking

  bit started;
  initial started = 1'b0;
  always @(posedge CLK) started <= 1'b1;

  default disable iff (!started);

  // Correct 1-cycle capture when data is known
  assert property ( !$isunknown($past(D)) |-> (Q == $past(D)) );

  // If data was unknown at capture, Q must be unknown on the next edge
  assert property ( $isunknown($past(D)) |-> $isunknown(Q) );

  // Any Q change must be explained by prior D differing from prior Q
  assert property ( (Q != $past(Q)) |-> ($past(D) != $past(Q)) );

  // Coverage: capture both 0 and 1, and observe a toggle on Q
  cover property ( !$isunknown($past(D)) && ($past(D) == 1'b0) && (Q == 1'b0) );
  cover property ( !$isunknown($past(D)) && ($past(D) == 1'b1) && (Q == 1'b1) );
  cover property ( Q != $past(Q) );

endmodule

// Bind into the DUT
bind dff dff_sva dff_sva_i(.D(D), .CLK(CLK), .Q(Q));