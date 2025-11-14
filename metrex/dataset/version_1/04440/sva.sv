// SVA for altera_tse_reset_synchronizer
// Bind-in assertions; concise but with full functional coverage

module sva_altera_tse_reset_synchronizer
  #(parameter ASYNC_RESET = 1,
    parameter DEPTH = 2)
(
  input  logic                   clk,
  input  logic                   reset_in,
  input  logic                   reset_out,
  input  logic [DEPTH-1:0]       altera_tse_reset_synchronizer_chain,
  input  logic                   altera_tse_reset_synchronizer_chain_out
);

  // Parameter sanity
  initial assert (DEPTH >= 2)
    else $error("DEPTH must be >= 2");

  // No X on observable output at clock edges
  assert property (@(posedge clk) !$isunknown(reset_out));

  generate if (ASYNC_RESET) begin : SVA_ASYNC

    // Async dominance: whenever reset_in is high, chain and output are 1
    assert property (@(posedge clk or posedge reset_in)
                     reset_in |-> (reset_out &&
                                   (altera_tse_reset_synchronizer_chain === {DEPTH{1'b1}})));

    // Synchronous deassert: exactly DEPTH clocks after first low, output deasserts
    sequence s_first_low;
      (!reset_in && $past(reset_in));
    endsequence

    assert property (@(posedge clk)
                     s_first_low |-> (reset_out[* (DEPTH-1)] ##1 !reset_out));

    // Output never falls while reset_in is high
    assert property (@(posedge clk) reset_in |-> reset_out);

    // Once deasserted, stays low until reset reasserts
    assert property (@(posedge clk) (!reset_out && !reset_in) |-> (!reset_out until_with reset_in));

    // Shift behavior when not in reset
    assert property (@(posedge clk)
                     !reset_in |-> (altera_tse_reset_synchronizer_chain[DEPTH-2:0]
                                      == $past(altera_tse_reset_synchronizer_chain[DEPTH-1:1]) &&
                                    altera_tse_reset_synchronizer_chain[DEPTH-1] == 1'b0 &&
                                    reset_out == $past(altera_tse_reset_synchronizer_chain[0])));

    // Coverage: deassert sequence and immediate assert on async reset
    cover property (@(posedge clk) s_first_low ##[1:DEPTH] !reset_out);
    cover property (@(posedge clk or posedge reset_in) $rose(reset_in) && reset_out);

  end else begin : SVA_SYNC

    // Output equals input delayed by DEPTH cycles
    assert property (@(posedge clk) reset_out == $past(reset_in, DEPTH));

    // Shift behavior every cycle
    assert property (@(posedge clk)
                     altera_tse_reset_synchronizer_chain[DEPTH-2:0]
                        == $past(altera_tse_reset_synchronizer_chain[DEPTH-1:1]) &&
                     altera_tse_reset_synchronizer_chain[DEPTH-1] == reset_in &&
                     reset_out == $past(altera_tse_reset_synchronizer_chain[0]));

    // Coverage: both polarities propagate through the chain
    cover property (@(posedge clk) $rose(reset_in) ##DEPTH $rose(reset_out));
    cover property (@(posedge clk) $fell(reset_in) ##DEPTH $fell(reset_out));

  end endgenerate

endmodule

bind altera_tse_reset_synchronizer
  sva_altera_tse_reset_synchronizer #(.ASYNC_RESET(ASYNC_RESET), .DEPTH(DEPTH))
  sva_i (
    .clk(clk),
    .reset_in(reset_in),
    .reset_out(reset_out),
    .altera_tse_reset_synchronizer_chain(altera_tse_reset_synchronizer_chain),
    .altera_tse_reset_synchronizer_chain_out(altera_tse_reset_synchronizer_chain_out)
  );