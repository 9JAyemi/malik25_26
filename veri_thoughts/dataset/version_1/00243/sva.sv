// SVA for up_down_counter
module up_down_counter_sva (
  input logic        UD,
  input logic        RST,   // active-low async reset
  input logic        clk,
  input logic [3:0]  Q,
  input logic        OVF
);

default clocking cb @(posedge clk); endclocking

// Knownness checks
assert property (cb !$isunknown({Q,OVF}));
assert property (cb disable iff (!RST) !$isunknown(UD));

// Async reset clears immediately on negedge
assert property (@(negedge RST) ##0 (Q==4'h0 && OVF==1'b0));

// Hold-low while in reset
assert property (cb (!RST) |-> (Q==4'h0 && OVF==1'b0));

// Next-state functional check (mod-16 up/down)
assert property (cb disable iff (!RST)
  Q == ($past(Q,1,4'h0) + (UD ? 4'd1 : 4'hF))
);

// OVF correctness: asserted only on wrap events
assert property (cb disable iff (!RST)
  OVF == ((UD  && ($past(Q,1,4'h0)==4'hF)) ||
          (!UD && ($past(Q,1,4'h0)==4'h0)))
);

// Minimal functional coverage
cover property (cb disable iff (!RST) (UD  && $past(Q,1,4'h0)==4'hF && OVF && Q==4'h0)); // up wrap
cover property (cb disable iff (!RST) (!UD && $past(Q,1,4'h0)==4'h0 && OVF && Q==4'hF)); // down wrap
cover property (cb disable iff (!RST) (UD  && $past(Q,1,4'h0)!=4'hF && !OVF && Q==$past(Q,1,4'h0)+1));
cover property (cb disable iff (!RST) (!UD && $past(Q,1,4'h0)!=4'h0 && !OVF && Q==$past(Q,1,4'h0)-1));

endmodule

// Bind into DUT
bind up_down_counter up_down_counter_sva sva_i (.*);