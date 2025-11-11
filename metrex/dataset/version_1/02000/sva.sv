// SVA for bitwise_and — concise, high-quality checks and coverage.
// Bind these assertions into the DUT to access internal nets.

checker bitwise_and_sva #(int WIDTH=8)(
  input logic                  clk,
  input logic [WIDTH-1:0]      input_a,
  input logic [WIDTH-1:0]      input_b,
  input logic [WIDTH-1:0]      output_result,
  // internal nets (8x WIDTH-wide as written in the DUT)
  input logic [WIDTH-1:0]      wire_and0,
  input logic [WIDTH-1:0]      wire_and1,
  input logic [WIDTH-1:0]      wire_and2,
  input logic [WIDTH-1:0]      wire_and3,
  input logic [WIDTH-1:0]      wire_and4,
  input logic [WIDTH-1:0]      wire_and5,
  input logic [WIDTH-1:0]      wire_and6,
  input logic [WIDTH-1:0]      wire_and7
);
  default clocking cb @(posedge clk); endclocking

  // Core functional equivalence (4-state aware)
  assert property (output_result === (input_a & input_b))
    else $error("bitwise_and: output_result != input_a & input_b");

  // If inputs are known, output must be known
  assert property (!$isunknown({input_a,input_b}) |-> !$isunknown(output_result))
    else $error("bitwise_and: X/Z on output with known inputs");

  // Internal net correctness (only bit[0] is functionally relevant; upper bits should be 0 due to width extension)
  assert property (wire_and0[0] === (input_a[0] & input_b[0]));  assert property (wire_and0[WIDTH-1:1] == '0);
  assert property (wire_and1[0] === (input_a[1] & input_b[1]));  assert property (wire_and1[WIDTH-1:1] == '0);
  assert property (wire_and2[0] === (input_a[2] & input_b[2]));  assert property (wire_and2[WIDTH-1:1] == '0);
  assert property (wire_and3[0] === (input_a[3] & input_b[3]));  assert property (wire_and3[WIDTH-1:1] == '0);
  assert property (wire_and4[0] === (input_a[4] & input_b[4]));  assert property (wire_and4[WIDTH-1:1] == '0);
  assert property (wire_and5[0] === (input_a[5] & input_b[5]));  assert property (wire_and5[WIDTH-1:1] == '0);
  assert property (wire_and6[0] === (input_a[6] & input_b[6]));  assert property (wire_and6[WIDTH-1:1] == '0);
  assert property (wire_and7[0] === (input_a[7] & input_b[7]));  assert property (wire_and7[WIDTH-1:1] == '0);

  // Output is driven from the intended internal net LSBs
  assert property (output_result[0] === wire_and0[0]);
  assert property (output_result[1] === wire_and1[0]);
  assert property (output_result[2] === wire_and2[0]);
  assert property (output_result[3] === wire_and3[0]);
  assert property (output_result[4] === wire_and4[0]);
  assert property (output_result[5] === wire_and5[0]);
  assert property (output_result[6] === wire_and6[0]);
  assert property (output_result[7] === wire_and7[0]);

  // Compact truth-table coverage per bit (00, 01, 10, 11 → result)
  genvar i;
  generate
    for (i = 0; i < WIDTH; i++) begin : gen_cov
      cover property (input_a[i]==0 && input_b[i]==0 && output_result[i]==0);
      cover property (input_a[i]==0 && input_b[i]==1 && output_result[i]==0);
      cover property (input_a[i]==1 && input_b[i]==0 && output_result[i]==0);
      cover property (input_a[i]==1 && input_b[i]==1 && output_result[i]==1);
    end
  endgenerate

  // Vector-level corners
  cover property (input_a == '0    && input_b == '0    && output_result == '0);
  cover property (input_a == '1    && input_b == '1    && output_result == '1);
  cover property (input_a == 8'hAA && input_b == 8'h55 && output_result == 8'h00);
  cover property (input_a == 8'hF0 && input_b == 8'h0F && output_result == 8'h00);
endchecker

// Bind into the DUT (module name binding gives access to internal nets by name)
bind bitwise_and bitwise_and_sva #(.WIDTH(8)) bitwise_and_sva_i(
  .clk          (clk),
  .input_a      (input_a),
  .input_b      (input_b),
  .output_result(output_result),
  .wire_and0    (wire_and0),
  .wire_and1    (wire_and1),
  .wire_and2    (wire_and2),
  .wire_and3    (wire_and3),
  .wire_and4    (wire_and4),
  .wire_and5    (wire_and5),
  .wire_and6    (wire_and6),
  .wire_and7    (wire_and7)
);