// SVA checkers for adder/average/top_module
// Concise, combinational (no DUT clock required). Bind these into your design.
// Uses immediate assertions/covers in always_comb for robust combinational checking.

`ifndef SYNTHESIS

// ------------------------------------
// Checker for adder
// ------------------------------------
module adder_sva (
  input logic [7:0] a,
  input logic [7:0] b,
  input logic [7:0] sum
);
  // Functional equivalence and X-prop sanity
  always_comb begin
    assert (sum === (a + b)) else $error("adder: sum != a+b (4-state check)");
    if (!$isunknown({a,b})) assert (!$isunknown(sum)) else $error("adder: sum is X/Z with known inputs");
    // Lightweight coverage
    cover (a==8'h00 && b==8'h00 && sum==8'h00);                 // zero
    cover (a==8'hFF && b==8'h01 && sum==8'h00);                 // wrap
    cover (a==8'h7F && b==8'h01 && sum==8'h80);                 // sign boundary
    cover ( ({1'b0,a}+{1'b0,b})[8] );                           // carry out
    cover (!({1'b0,a}+{1'b0,b})[8] );                           // no carry
  end
endmodule

// ------------------------------------
// Checker for average (two-stage sum)
// ------------------------------------
module average_sva (
  input logic [7:0] a,
  input logic [7:0] b,
  input logic [7:0] c,
  input logic [7:0] sum,     // internal stage-1 sum
  input logic [7:0] result,
  input logic [7:0] divisor  // constant in DUT (unused functionally)
);
  // Stagewise functional checks and X-prop sanity
  always_comb begin
    assert (sum    === (a + b)) else $error("average: stage1 sum != a+b");
    assert (result === (sum + c)) else $error("average: stage2 result != sum+c");
    if (!$isunknown({a,b}))      assert (!$isunknown(sum))    else $error("average: stage1 sum X/Z with known inputs");
    if (!$isunknown({sum,c}))    assert (!$isunknown(result)) else $error("average: result X/Z with known inputs");
    assert (divisor === 8'd3) else $error("average: divisor changed from 3");

    // Coverage of key arithmetic corner cases
    cover ( ({1'b0,a}+{1'b0,b})[8] );                          // carry in stage1
    cover ( ({1'b0,sum}+{1'b0,c})[8] );                        // carry in stage2
    cover ( ({1'b0,a}+{1'b0,b}+{1'b0,c})[8] );                 // end-to-end carry
    cover (!({1'b0,a}+{1'b0,b}+{1'b0,c})[8] );                 // end-to-end no carry
    cover (a==8'hFF && b==8'hFF && c==8'hFF && result==8'hFD); // triple max -> 765 % 256 = 253
  end
endmodule

// ------------------------------------
// Checker for top_module (end-to-end)
// ------------------------------------
module top_sva (
  input logic [7:0] a,
  input logic [7:0] b,
  input logic [7:0] c,
  input logic [7:0] result
);
  always_comb begin
    assert (result === ((a + b) + c)) else $error("top: result != a+b+c");
    if (!$isunknown({a,b,c})) assert (!$isunknown(result)) else $error("top: result X/Z with known inputs");

    // Minimal end-to-end coverage
    cover (a==8'h00 && b==8'h00 && c==8'h00 && result==8'h00);
    cover ( ({1'b0,a}+{1'b0,b}+{1'b0,c})[8] );                 // any overflow
    cover (!({1'b0,a}+{1'b0,b}+{1'b0,c})[8] );                 // no overflow
  end
endmodule

// ------------------------------------
// Bind checkers into DUT
// ------------------------------------
bind adder       adder_sva   u_adder_sva   (.a(a), .b(b), .sum(sum));
bind average     average_sva u_average_sva (.a(a), .b(b), .c(c), .sum(sum), .result(result), .divisor(divisor));
bind top_module  top_sva     u_top_sva     (.a(a), .b(b), .c(c), .result(result));

`endif