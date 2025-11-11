// SVA for counter
module counter_sva (
  input logic       CLK,
  input logic       RST,
  input logic       EN,
  input logic [3:0] COUNT
);

  // Track a clean "past" window that is reset-aware (including async pulses)
  logic past_valid;
  always_ff @(posedge CLK or posedge RST) begin
    if (RST) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  default clocking cb @(posedge CLK); endclocking

  // Async reset: immediate zero on posedge RST and zero while RST is high
  assert property (@(posedge RST) COUNT == 4'h0 && !$isunknown(COUNT));
  assert property (RST |-> COUNT == 4'h0);

  // Next-state function when not in/just-after reset
  assert property (disable iff (RST || !past_valid)
                   COUNT == $past(COUNT) + (EN ? 4'd1 : 4'd0));

  // Reset has priority over EN on clock edge
  assert property ((RST && EN) |-> COUNT == 4'h0);

  // Knownness
  assert property (!$isunknown(COUNT));

  // Coverage
  cover property (@(posedge RST) 1);
  cover property (disable iff (RST || !past_valid) EN  && COUNT == $past(COUNT) + 1);
  cover property (disable iff (RST || !past_valid) !EN && COUNT == $past(COUNT));
  cover property (disable iff (RST || !past_valid) ($past(COUNT) == 4'hF && EN && COUNT == 4'h0));

endmodule

bind counter counter_sva u_counter_sva(.CLK(CLK), .RST(RST), .EN(EN), .COUNT(COUNT));