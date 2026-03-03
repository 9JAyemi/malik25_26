// SVA for binary_counter
module binary_counter_sva (
  input  logic       clk,
  input  logic       reset,     // active-low in DUT; here 1=deasserted, 0=asserted
  input  logic [3:0] count_out
);

  // Async reset drives 0 immediately on negedge reset
  assert property (@(negedge reset) 1'b1 |-> ##0 (count_out == 4'h0))
    else $error("count_out not cleared immediately on async reset assert");

  // While in reset, output must be 0 at each clk edge
  assert property (@(posedge clk) !reset |-> (count_out == 4'h0))
    else $error("count_out not held at 0 while reset asserted");

  // No X/Z during normal operation
  assert property (@(posedge clk) reset |-> !$isunknown(count_out))
    else $error("count_out has X/Z during normal operation");

  // First active clock after reset deassertion must produce 1
  assert property (@(posedge clk) $rose(reset) |-> (count_out == 4'h1))
    else $error("First count after reset deassert is not 1");

  // Increment by 1 when not wrapping (and not just out of reset)
  assert property (@(posedge clk)
                   reset && $past(reset) && ($past(count_out) != 4'hF)
                   |-> (count_out == $past(count_out) + 4'd1))
    else $error("Count failed to increment by 1");

  // Wrap 15 -> 0
  assert property (@(posedge clk)
                   reset && $past(reset) && ($past(count_out) == 4'hF)
                   |-> (count_out == 4'h0))
    else $error("Count failed to wrap from 15 to 0");

  // No mid-cycle glitches when reset is high
  assert property (@(negedge clk) reset |-> $stable(count_out))
    else $error("count_out changed away from posedge clk");

  // -------------------------
  // Functional coverage
  // -------------------------

  // See both reset edges
  cover property (@(posedge clk) $fell(reset));
  cover property (@(posedge clk) $rose(reset));

  // Cover wraparound and post-reset first increment
  cover property (@(posedge clk) reset && $past(reset) && ($past(count_out)==4'hF)
                               ##1 reset && (count_out==4'h0));
  cover property (@(posedge clk) $rose(reset) ##1 (reset && count_out==4'h1));

  // Cover a full 16-step cycle after a reset release
  cover property (@(posedge clk) $rose(reset)
                  ##1 (reset && count_out==4'h1)
                  ##15 (reset && count_out==4'h0));

  // Cover all 16 count values under normal operation
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : g_val_cov
      cover property (@(posedge clk) reset && (count_out == i[3:0]));
    end
  endgenerate

endmodule

// Bind into DUT
bind binary_counter binary_counter_sva u_binary_counter_sva (
  .clk      (clk),
  .reset    (reset),
  .count_out(count_out)
);