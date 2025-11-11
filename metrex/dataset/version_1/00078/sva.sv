// SVA checker for Divider. Bind this to the DUT.
// Example bind (adjust hierarchical names as needed):
// bind Divider Divider_sva #(.n(n)) u_div_sva (.* , .clk(tb_clk), .rst_n(tb_rst_n));

module Divider_sva #(parameter int n = 8) (
  input logic                       clk,
  input logic                       rst_n,
  input  logic signed [n-1:0]       div,
  input  logic signed [n-1:0]       dvsr,
  input  logic signed [n-1:0]       quot,
  input  logic signed [n-1:0]       rem
);

  default clocking cb @(posedge clk); endclocking

  localparam logic signed [n-1:0] MIN_NEG = {1'b1,{(n-1){1'b0}}};

  function automatic logic signed [n:0] sext(input logic signed [n-1:0] a);
    return {a[n-1],a};
  endfunction

  function automatic logic [n:0] abs_ext(input logic signed [n-1:0] a);
    logic signed [n:0] ae = sext(a);
    return ae[n] ? logic'(-ae) : logic'(ae);
  endfunction

  // 1) Divide-by-zero must drive Xs; otherwise outputs must be known
  assert property (disable iff (!rst_n) (dvsr == 0) |-> ($isunknown(quot) && $isunknown(rem)));
  assert property (disable iff (!rst_n) (dvsr != 0) |-> (!$isunknown(quot) && !$isunknown(rem)));

  // 2) Functional equivalence to signed division/modulus operators
  assert property (disable iff (!rst_n) (dvsr != 0) |-> (quot == (div / dvsr) && rem == (div % dvsr)));

  // 3) Fundamental identity in n-bit signed arithmetic
  assert property (disable iff (!rst_n) (dvsr != 0) |-> (div == (quot * dvsr) + rem));

  // 4) Remainder properties
  assert property (disable iff (!rst_n) (dvsr != 0) |-> (abs_ext(rem) < abs_ext(dvsr)));
  assert property (disable iff (!rst_n) (dvsr != 0) |-> (rem == '0 || (rem[n-1] == div[n-1])));

  // 5) Useful corner cases
  assert property (disable iff (!rst_n) (dvsr ==  1) |-> (quot == div && rem == 0));
  assert property (disable iff (!rst_n) (dvsr == -1 && div != MIN_NEG) |-> (quot == -div && rem == 0));
  assert property (disable iff (!rst_n) (dvsr != 0 && div == 0) |-> (quot == 0 && rem == 0));
  assert property (disable iff (!rst_n) (dvsr != 0 && (abs_ext(div) < abs_ext(dvsr))) |-> (quot == 0 && rem == div));

  // Coverage: exercise all quadrants, zeros, and key edges
  cover property (disable iff (!rst_n) (dvsr == 0));
  cover property (disable iff (!rst_n) (dvsr != 0 && div >= 0 && dvsr > 0));
  cover property (disable iff (!rst_n) (dvsr != 0 && div <  0 && dvsr < 0));
  cover property (disable iff (!rst_n) (dvsr != 0 && div <  0 && dvsr > 0));
  cover property (disable iff (!rst_n) (dvsr != 0 && div >= 0 && dvsr < 0));
  cover property (disable iff (!rst_n) (dvsr != 0 && rem == 0));
  cover property (disable iff (!rst_n) (dvsr != 0 && quot == 0));
  cover property (disable iff (!rst_n) (dvsr == -1 && div == MIN_NEG));
endmodule