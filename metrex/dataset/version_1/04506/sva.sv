// SVA for binary_counter_4bit
module binary_counter_4bit_sva (
  input logic       CLK,
  input logic       RST,
  input logic       EN,
  input logic [3:0] Q
);

  default clocking cb @(posedge CLK); endclocking

  logic past_valid;
  always @(posedge CLK) past_valid <= 1'b1;

  // Sanity: no X on key signals at clock edge
  assert property (cb !$isunknown({RST,EN,Q}));

  // Synchronous reset
  assert property (cb past_valid && RST |-> (Q == 4'd0));

  // Enable: increment by 1 (mod-16)
  assert property (cb past_valid && !RST && EN |-> (Q == $past(Q) + 4'd1));

  // Hold when not enabled
  assert property (cb past_valid && !RST && !EN |-> (Q == $past(Q)));

  // Optional: no glitches between clocks
  assert property (@(negedge CLK) $stable(Q));

  // Coverage
  cover property (cb past_valid && !RST && EN && (Q == $past(Q) + 4'd1));           // saw an increment
  cover property (cb past_valid && !RST && !EN && (Q == $past(Q)));                 // saw a hold
  cover property (cb past_valid && !RST && EN && ($past(Q) == 4'hF) && (Q == 4'h0)); // wrap 15->0
  cover property (cb past_valid && ($past(Q) != 4'd0) && RST && (Q == 4'd0));        // reset from nonzero

endmodule

// Bind into DUT
bind binary_counter_4bit binary_counter_4bit_sva sva_i (.*);