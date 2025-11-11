// SVA checker for parity_generator
module parity_generator_sva (
  input logic [15:0] data,
  input logic [16:0] parity_data
);

  // Sample on any relevant combinational change
  event comb_ev;
  always @(data or parity_data) -> comb_ev;

  // Functional equivalence (primary check)
  property p_concat;
    parity_data == {^data, data};
  endproperty
  assert property (@(comb_ev) p_concat)
    else $error("parity_data != {^data, data}");

  // Redundant but diagnostic checks
  assert property (@(comb_ev) parity_data[15:0] == data)
    else $error("Lower 16 bits mismatch data");
  assert property (@(comb_ev) parity_data[16] == ^data)
    else $error("Parity bit != XOR of data");

  // Even parity across the full 17-bit word
  assert property (@(comb_ev) (^parity_data) == 1'b0)
    else $error("Overall XOR of parity_data != 0 (not even parity)");

  // Clean output when input is clean (no X/Z propagation)
  assert property (@(comb_ev) !$isunknown(data) |-> !$isunknown(parity_data))
    else $error("parity_data has X/Z while data is clean");

  // Coverage
  cover property (@(comb_ev) parity_data[16] == 1'b0);                 // even data parity
  cover property (@(comb_ev) parity_data[16] == 1'b1);                 // odd data parity
  cover property (@(comb_ev) data == 16'h0000 && parity_data == 17'h0);
  cover property (@(comb_ev) data == 16'hFFFF && parity_data == {1'b0,16'hFFFF});
  cover property (@(comb_ev) $onehot(data) && parity_data[16] == 1'b1);

endmodule

bind parity_generator parity_generator_sva parity_generator_sva_i (.data(data), .parity_data(parity_data));