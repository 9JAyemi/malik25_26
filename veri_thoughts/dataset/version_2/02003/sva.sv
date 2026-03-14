module byte_generator_even_parity_sva (
  input logic clk,
  input logic reset,
  input logic [7:0] data_in,
  input logic [8:0] byte_out
);

  ///// Reset behavior /////
  // When reset is asserted, byte_out must be all zeros.
  reset_clears_output: assert property (
    @(posedge clk) reset |-> (byte_out == 9'b0)
  );

  ///// Functional mapping /////
  // Next cycle, byte_out[7:0] equals data_in from the previous cycle.
  map_lower_byte_next: assert property (
    @(posedge clk) disable iff (reset) 1'b1 |=> (byte_out[7:0] == $past(data_in))
  );

  // Next cycle, byte_out[8] equals XOR-reduction of previous cycle's data_in.
  map_parity_next: assert property (
    @(posedge clk) disable iff (reset) 1'b1 |=> (byte_out[8] == ^$past(data_in))
  );

  ///// Parity consistency /////
  // Parity bit matches XOR of the stored data bits.
  parity_matches_lower_bits: assert property (
    @(posedge clk) disable iff (reset) (byte_out[8] == ^byte_out[7:0])
  );

  // The 9-bit byte_out always has even parity.
  even_parity_invariant: assert property (
    @(posedge clk) disable iff (reset) (^byte_out == 1'b0)
  );

  ///// Stability relation /////
  // If data_in is the same across two cycles, byte_out remains unchanged next cycle.
  output_stable_when_input_stable: assert property (
    @(posedge clk) disable iff (reset) (data_in == $past(data_in)) |=> (byte_out == $past(byte_out))
  );

endmodule