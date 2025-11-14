// SVA for xor_32. Bind this to the DUT and provide a sampling clock/reset.
module xor_32_sva #(parameter WIDTH=32)
(
  input  logic                 clk,
  input  logic                 rst_n,
  input  logic [WIDTH-1:0]     a,
  input  logic [WIDTH-1:0]     b,
  input  logic [WIDTH-1:0]     out
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Functional correctness (when inputs are known)
  assert property (!$isunknown({a,b}) |-> out === (a ^ b))
    else $error("xor_32: out != a ^ b");

  // Output must not change unless inputs change
  assert property ($stable({a,b}) |-> $stable(out))
    else $error("xor_32: out changed while inputs stable");

  // Output must be known when inputs are known
  assert property (!$isunknown({a,b}) |-> !$isunknown(out))
    else $error("xor_32: out has X/Z while inputs are known");

  // Useful corollaries
  assert property (!$isunknown({a,b}) && (a == b)  |-> out == '0);
  assert property (!$isunknown({a,b}) && (a == ~b) |-> out == '1);

  // Coverage: key vector cases
  cover property (!$isunknown({a,b}) && (a == b)  && (out == '0));
  cover property (!$isunknown({a,b}) && (a == ~b) && (out == '1));

  // Per-bit truth-table coverage (00->0, 01->1, 10->1, 11->0)
  genvar i;
  generate
    for (i = 0; i < WIDTH; i++) begin : bit_cov
      cover property (!$isunknown({a[i],b[i]}) && (a[i]==1'b0) && (b[i]==1'b0) && (out[i]==1'b0));
      cover property (!$isunknown({a[i],b[i]}) && (a[i]==1'b0) && (b[i]==1'b1) && (out[i]==1'b1));
      cover property (!$isunknown({a[i],b[i]}) && (a[i]==1'b1) && (b[i]==1'b0) && (out[i]==1'b1));
      cover property (!$isunknown({a[i],b[i]}) && (a[i]==1'b1) && (b[i]==1'b1) && (out[i]==1'b0));
    end
  endgenerate

endmodule

// Example bind (provide tb_clk/tb_rst_n in your environment):
// bind xor_32 xor_32_sva #(.WIDTH(32)) u_xor_32_sva ( .clk(tb_clk), .rst_n(tb_rst_n), .a(a), .b(b), .out(out) );