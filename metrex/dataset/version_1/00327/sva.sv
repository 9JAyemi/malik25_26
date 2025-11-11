// SVA for binary_to_gray. Bind this module to the DUT instance.
// Provide a sampling clock from your environment (clk).

module binary_to_gray_sva #(parameter WIDTH = 8)
(
  input  logic                 clk,
  input  logic [WIDTH-1:0]     binary_in,
  input  logic [WIDTH-1:0]     gray_out
);

  default clocking cb @(posedge clk); endclocking

  // Basic functional correctness (when inputs are known)
  assert property (!$isunknown(binary_in)
                   |-> (gray_out == (binary_in ^ {1'b0, binary_in[WIDTH-1:1]})));

  // No X/Z propagation to output when inputs are clean
  assert property (!$isunknown(binary_in) |-> !$isunknown(gray_out));

  // Combinational determinism: if input is stable over a cycle, output is stable
  assert property ($stable(binary_in) |-> $stable(gray_out));

  // Gray-code adjacency: +/-1 (no wrap) on binary causes exactly one output bit to toggle
  // Exclude wrap cases 0xFF->0x00 and 0x00->0xFF
  localparam logic [WIDTH-1:0] ALL1 = {WIDTH{1'b1}};
  localparam logic [WIDTH-1:0] ALL0 = {WIDTH{1'b0}};
  assert property (
    !$isunknown(binary_in) && !$isunknown($past(binary_in)) &&
    !($past(binary_in)==ALL1 && binary_in==ALL0) &&
    !(binary_in==ALL1 && $past(binary_in)==ALL0) &&
    ( (binary_in == $past(binary_in) + 1) ||
      ($past(binary_in) == binary_in + 1) )
    |-> $onehot(gray_out ^ $past(gray_out))
  );

  // Bit-level mapping checks (redundant but pinpoint failures)
  genvar i;
  for (i = 0; i < WIDTH-1; i++) begin : g_bitmap
    assert property (!$isunknown(binary_in)
                     |-> (gray_out[i] == (binary_in[i] ^ binary_in[i+1])));
  end
  assert property (!$isunknown(binary_in) |-> (gray_out[WIDTH-1] == binary_in[WIDTH-1]));

  // Minimal but meaningful coverage
  cover property (binary_in==ALL0 && gray_out==ALL0);                 // zero
  cover property (binary_in==ALL1 && gray_out=={1'b1,{(WIDTH-1){1'b0}}}); // max -> MSB only
  cover property ( (binary_in == $past(binary_in)+1) &&
                   !($past(binary_in)==ALL1 && binary_in==ALL0) &&
                   $onehot(gray_out ^ $past(gray_out)) );             // observed +1 adjacency
  for (i = 0; i < WIDTH; i++) begin : g_cov_bits
    cover property ($changed(gray_out[i]));                           // each Gray bit toggles
  end

endmodule

// Example bind (replace <inst> and <clk> with your instance/clock):
// bind binary_to_gray binary_to_gray_sva #(.WIDTH(8)) b2g_sva (.<clk>(<clk>), .binary_in(binary_in), .gray_out(gray_out));