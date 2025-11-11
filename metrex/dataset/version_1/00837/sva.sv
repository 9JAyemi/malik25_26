// SVA checker for binary_to_bcd_converter
module b2bcd_sva (
  input logic        clk,
  input logic        rst_n,         // tie high if no reset
  input logic [3:0]  binary_in,
  input logic [3:0]  bcd_out,
  input logic        greater_than_nine
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Knownness: for known input, outputs must be known
  assert property ( !$isunknown(binary_in) |-> !$isunknown({bcd_out, greater_than_nine}) );

  // Flag correctness
  assert property ( !$isunknown(binary_in) |-> (greater_than_nine == (binary_in > 4'd9)) );

  // Functional mapping
  assert property ( !$isunknown(binary_in) && (binary_in <= 4'd9)
                    |-> (bcd_out == binary_in && !greater_than_nine) );
  assert property ( !$isunknown(binary_in) && (binary_in >= 4'd10)
                    |-> (bcd_out == (binary_in - 4'd10) && greater_than_nine) );

  // BCD digit bound
  assert property ( !$isunknown(binary_in) |-> (bcd_out <= 4'd9) );

  // Stability: if input holds, outputs hold (combinational, no state)
  assert property ( !$isunknown({binary_in,$past(binary_in)}) && (binary_in == $past(binary_in))
                    |-> {bcd_out,greater_than_nine} == $past({bcd_out,greater_than_nine}) );

  // Coverage: hit all input values and both ranges
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cv
      cover property (binary_in == i[3:0]);
    end
  endgenerate
  cover property ( (binary_in <= 4'd9)  && (bcd_out == binary_in) && !greater_than_nine );
  cover property ( (binary_in >= 4'd10) && (bcd_out == (binary_in - 4'd10)) && greater_than_nine );

endmodule

// Bind template (connect clk/rst as appropriate):
// bind binary_to_bcd_converter b2bcd_sva u_b2bcd_sva ( .clk(tb_clk), .rst_n(1'b1),
//   .binary_in(binary_in), .bcd_out(bcd_out), .greater_than_nine(greater_than_nine) );