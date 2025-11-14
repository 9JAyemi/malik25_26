// SVA checker for altera_reset_synchronizer
module altera_reset_synchronizer_sva #(parameter ASYNC_RESET=1, parameter int DEPTH=2)
(
  input logic clk,
  input logic reset_in,
  input logic reset_out
);

  default clocking cb @(posedge clk); endclocking

  generate
    if (ASYNC_RESET) begin : g_async
      // Async assertion: output must go high immediately on posedge reset_in
      assert property (@(posedge reset_in) ##0 reset_out);

      // While reset_in is high, reset_out must be high
      assert property (reset_in |-> reset_out);

      // After reset deasserts, reset_out stays 1 for DEPTH clocks, then falls on the next clock
      sequence s_hold_out_1_for_depth;
        repeat (DEPTH) @(posedge clk) reset_out;
      endsequence
      assert property (@(negedge reset_in) s_hold_out_1_for_depth ##1 @(posedge clk) !reset_out);

      // If input is low for DEPTH+1 clocks, output must be low now
      assert property (!reset_in [* (DEPTH+1)] |-> !reset_out);
    end else begin : g_sync
      // A change on reset_out implies input held that value for DEPTH+1 prior clocks
      assert property ($rose(reset_out) |-> reset_in  [* (DEPTH+1)]);
      assert property ($fell(reset_out) |-> !reset_in [* (DEPTH+1)]);

      // If input is stable for DEPTH+1 clocks, output equals it
      assert property ( reset_in  [* (DEPTH+1)] |->  reset_out);
      assert property (!reset_in [* (DEPTH+1)] |-> !reset_out);
    end
  endgenerate

  // Basic liveness covers
  cover property (@(posedge clk) $fell(reset_in) ##[1:$] $fell(reset_out));
  cover property (@(posedge clk) $rose(reset_in) ##[1:$] $rose(reset_out));

endmodule

bind altera_reset_synchronizer
  altera_reset_synchronizer_sva #(.ASYNC_RESET(ASYNC_RESET), .DEPTH(DEPTH)) u_sva (.*);


// Optional internal checks (paste inside DUT, or wrap with a bind that exposes these regs)
`ifdef SVA_INTERNAL
  generate
    if (ASYNC_RESET) begin : g_int_async
      // Shift behavior when not in async reset; zero enters MSB; out follows prior LSB
      assert property (@(posedge clk) disable iff (reset_in)
        altera_reset_synchronizer_int_chain[DEPTH-2:0] == $past(altera_reset_synchronizer_int_chain[DEPTH-1:1]) &&
        altera_reset_synchronizer_int_chain[DEPTH-1]   == 1'b0 &&
        altera_reset_synchronizer_int_chain_out        == $past(altera_reset_synchronizer_int_chain[0]));

      // Immediate async set of chain and out on posedge reset_in
      assert property (@(posedge reset_in) ##0
        altera_reset_synchronizer_int_chain == {DEPTH{1'b1}} &&
        altera_reset_synchronizer_int_chain_out);
    end else begin : g_int_sync
      // Shift behavior; input enters MSB; out follows prior LSB
      assert property (@(posedge clk)
        altera_reset_synchronizer_int_chain[DEPTH-2:0] == $past(altera_reset_synchronizer_int_chain[DEPTH-1:1]) &&
        altera_reset_synchronizer_int_chain[DEPTH-1]   == $past(reset_in) &&
        altera_reset_synchronizer_int_chain_out        == $past(altera_reset_synchronizer_int_chain[0]));
    end
  endgenerate
`endif