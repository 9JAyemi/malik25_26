// SVA checker for binary_to_gray
// Bind this to your DUT instance and connect a clock/reset from your environment.

module binary_to_gray_sva
  (
    input logic               clk,
    input logic               rst_n,
    input logic [7:0]         binary,
    input logic [7:0]         gray
  );

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  localparam int WIDTH = 8;

  // Helper: gray->binary (inverse)
  function automatic logic [WIDTH-1:0] gray2bin (input logic [WIDTH-1:0] g);
    logic [WIDTH-1:0] b;
    b[WIDTH-1] = g[WIDTH-1];
    for (int i = WIDTH-2; i >= 0; i--) b[i] = b[i+1] ^ g[i];
    return b;
  endfunction

  // Sanity: known-propagation when inputs are known
  assert property (!$isunknown(binary) |-> !$isunknown(gray));

  // Functional equivalence
  assert property (gray == (binary ^ {1'b0, binary[WIDTH-1:1]}));

  // Bitwise decomposition checks
  assert property (gray[WIDTH-1] == binary[WIDTH-1]);
  generate
    genvar i;
    for (i = 0; i < WIDTH-1; i++) begin : gen_bitwise
      assert property (gray[i] == (binary[i] ^ binary[i+1]));
    end
  endgenerate

  // Inverse mapping is consistent
  assert property (!$isunknown(gray) |-> gray2bin(gray) == binary);

  // Gray-code property on +1 binary increments (including wrap): exactly one bit toggles
  assert property (!$isunknown({binary,$past(binary)}) && (binary == $past(binary)+1)
                   |-> $onehot(gray ^ $past(gray)));

  // Coverage
  // - Each input/output bit toggles at least once
  generate
    for (i = 0; i < WIDTH; i++) begin : gen_cov_bits
      cover property ($rose(binary[i]));
      cover property ($fell(binary[i]));
      cover property ($rose(gray[i]));
      cover property ($fell(gray[i]));
    end
  endgenerate
  // - Exercise corner values and wrap increment
  cover property (binary == '0);
  cover property (binary == '1);
  cover property (binary == {WIDTH{1'b1}});
  cover property ($past(binary) == {WIDTH{1'b1}} && binary == '0); // wrap
  cover property (binary == (1 << (WIDTH-1))); // MSB set

endmodule

// Example bind (adjust hierarchical clk/rst_n as appropriate):
// bind binary_to_gray binary_to_gray_sva u_sva (.clk(tb.clk), .rst_n(tb.rst_n), .binary(binary), .gray(gray));