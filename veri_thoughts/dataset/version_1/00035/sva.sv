// SVA checker for math_op. Bind to your DUT and provide a sampling clk/rst.
module math_op_sva #(parameter int W=8)(
  input logic                 clk,
  input logic                 rst_n,
  input logic [W-1:0]         a,
  input logic [W-1:0]         b,
  input logic [1:0]           op,
  input logic [W-1:0]         result
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Helper computations (mod-W truncation as in DUT)
  logic [W-1:0] add_w = (a + b) & {W{1'b1}};
  logic [W-1:0] sub_w = (a - b) & {W{1'b1}};
  logic [W-1:0] mul_w = (a * b) & {W{1'b1}};

  // Overflow/underflow indicators for coverage
  wire add_overflow = ({1'b0,a} + {1'b0,b})[W];
  wire sub_underflow = ({1'b0,a} - {1'b0,b})[W];
  wire mul_overflow = |((a*b) >> W);

  // Inputs-known => output-known (no X-propagation for fully known inputs)
  assert property (!$isunknown({a,b,op})) |-> !$isunknown(result));

  // Pure combinational functional correctness (all ops, mod-W semantics)
  assert property (result ==
                   (op==2'b00 ? add_w :
                    op==2'b01 ? sub_w :
                    op==2'b10 ? mul_w :
                                (b=={W{1'b0}} ? {W{1'b0}} : (a / b))));

  // Stability: if inputs are stable, result must be stable (no hidden state)
  assert property ($stable({a,b,op}) |-> $stable(result));

  // Functional branch checks (optional, more readable diagnostics)
  assert property ((op==2'b00) |-> result==add_w);
  assert property ((op==2'b01) |-> result==sub_w);
  assert property ((op==2'b10) |-> result==mul_w);
  assert property ((op==2'b11 && b==0) |-> result=={W{1'b0}});
  assert property ((op==2'b11 && b!=0) |-> result==(a/b));

  // Coverage: hit each operation and corner cases
  cover property (op==2'b00);
  cover property (op==2'b01);
  cover property (op==2'b10);
  cover property (op==2'b11 && b==0);
  cover property (op==2'b11 && b!=0);

  cover property (op==2'b00 && add_overflow);
  cover property (op==2'b01 && sub_underflow);
  cover property (op==2'b10 && mul_overflow);
  cover property (op==2'b11 && b==8'd1);
endmodule

// Example bind (adjust clk/rst paths as needed):
// bind math_op math_op_sva #(.W(8)) u_math_op_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));