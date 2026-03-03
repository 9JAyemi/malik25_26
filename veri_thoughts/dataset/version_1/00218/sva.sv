// SVA for signed_multiplier_32 and submodules
// Bind these assertion modules to the DUTs

// Top-level SVA: checks reset behavior, CE-gated update, hold, math equivalence,
// internal wiring, X-checks, and minimal functional coverage.
module signed_multiplier_32_sva #(
  parameter int din0_WIDTH = 1,
  parameter int din1_WIDTH = 1,
  parameter int dout_WIDTH = 1
)(
  input  logic                         clk,
  input  logic                         reset,
  input  logic                         ce,
  input  logic signed [din0_WIDTH-1:0] din0,
  input  logic signed [din1_WIDTH-1:0] din1,
  input  logic signed [dout_WIDTH+din0_WIDTH-1:0] dout,
  input  logic        [2*dout_WIDTH-1:0]          mul_result,
  input  logic signed [dout_WIDTH-1:0]            dout_int
);

  // Helper: truncates full-precision product into 2*dout_WIDTH signed bits
  function automatic logic signed [2*dout_WIDTH-1:0]
    trunc_prod(input logic signed [din0_WIDTH-1:0] a,
               input logic signed [din1_WIDTH-1:0] b);
    trunc_prod = $signed(a) * $signed(b);
  endfunction

  function automatic logic signed [dout_WIDTH-1:0]
    hi_half(input logic signed [2*dout_WIDTH-1:0] p);
    hi_half = p[2*dout_WIDTH-1:dout_WIDTH];
  endfunction

  // Parameter sanity
  initial begin
    assert (dout_WIDTH > 0 && din0_WIDTH > 0 && din1_WIDTH > 0)
      else $error("Width parameters must be > 0");
  end

  default clocking cb @(posedge clk); endclocking

  // X-checks
  assert property ( !$isunknown({reset,ce}) )
    else $error("X on control signals");
  assert property ( !reset |-> (!$isunknown(dout_int) && !$isunknown(dout)) )
    else $error("X on outputs when not in reset");

  // Reset clears to zero by next cycle; holds zero while reset remains asserted
  assert property ( reset |=> (dout_int == '0) )
    else $error("dout_int not cleared after reset");
  assert property ( reset && $past(reset) |-> (dout_int == '0 && $stable(dout_int)) )
    else $error("dout_int not held at zero during reset");
  // After reset deassertion and while CE=0, hold zero
  assert property ( !reset && $past(reset) && !ce |-> (dout_int == '0) )
    else $error("dout_int not zero after reset until first CE");

  // Functional: internal mul_result equals truncated product of inputs
  assert property ( $signed(mul_result) == trunc_prod(din0, din1) )
    else $error("mul_result != truncated product");

  // CE-gated register behavior
  // Update on CE using current-cycle inputs (observed next cycle)
  assert property ( disable iff (reset)
                    ce |=> ($signed(dout_int) == hi_half(trunc_prod(din0, din1))) )
    else $error("dout_int update mismatch when CE=1");

  // Hold when CE=0
  assert property ( disable iff (reset)
                    !ce |=> $stable(dout_int) )
    else $error("dout_int changed while CE=0");

  // Sign-extension to external dout matches dout_int
  // Compare as signed after explicit sign-extension
  localparam int DOUT_EXT_W = dout_WIDTH + din0_WIDTH;
  wire logic signed [DOUT_EXT_W-1:0] dout_int_sext =
    {{(DOUT_EXT_W-dout_WIDTH){dout_int[dout_WIDTH-1]}}, dout_int};
  assert property ( $signed(dout) == $signed(dout_int_sext) )
    else $error("dout sign-extension mismatch");

  // Minimal functional coverage
  // - CE-driven update occurs and changes value
  cover property ( disable iff (reset) ce ##1 $changed(dout_int) );
  // - Hold for several cycles with CE=0
  cover property ( disable iff (reset) !ce [*3] ##1 $stable(dout_int) );
  // - Exercise all sign combinations at update
  localparam int A_MSB = din0_WIDTH-1;
  localparam int B_MSB = din1_WIDTH-1;
  cover property ( disable iff (reset) ce && (din0[A_MSB]==0) && (din1[B_MSB]==0) );
  cover property ( disable iff (reset) ce && (din0[A_MSB]==1) && (din1[B_MSB]==0) );
  cover property ( disable iff (reset) ce && (din0[A_MSB]==0) && (din1[B_MSB]==1) );
  cover property ( disable iff (reset) ce && (din0[A_MSB]==1) && (din1[B_MSB]==1) );
  // - Exercise non-zero high-half (truncation/rounding relevance)
  cover property ( disable iff (reset) ce &&
                   (hi_half(trunc_prod(din0,din1)) != '0) );

endmodule

bind signed_multiplier_32
  signed_multiplier_32_sva #(
    .din0_WIDTH(din0_WIDTH),
    .din1_WIDTH(din1_WIDTH),
    .dout_WIDTH(dout_WIDTH)
  ) signed_multiplier_32_sva_i (.*);

// Mid-level SVA: p equals truncated product (combinational correctness) and X-check
module signed_multiplier_sva #(
  parameter int din0_WIDTH = 1,
  parameter int din1_WIDTH = 1,
  parameter int dout_WIDTH = 1
)(
  input  logic                         clk,
  input  logic                         ce,
  input  logic signed [din0_WIDTH-1:0] a,
  input  logic signed [din1_WIDTH-1:0] b,
  input  logic signed [2*dout_WIDTH-1:0] p
);
  function automatic logic signed [2*dout_WIDTH-1:0]
    trunc_prod(input logic signed [din0_WIDTH-1:0] a_i,
               input logic signed [din1_WIDTH-1:0] b_i);
    trunc_prod = $signed(a_i) * $signed(b_i);
  endfunction

  default clocking cb @(posedge clk); endclocking

  assert property ( $signed(p) == trunc_prod(a,b) )
    else $error("signed_multiplier.p != truncated product");

  assert property ( !$isunknown({a,b}) |-> !$isunknown(p) )
    else $error("X on p when inputs known");
endmodule

bind signed_multiplier
  signed_multiplier_sva #(
    .din0_WIDTH(din0_WIDTH),
    .din1_WIDTH(din1_WIDTH),
    .dout_WIDTH(dout_WIDTH)
  ) signed_multiplier_sva_i (.*);

// Leaf SVA: pure combinational multiply correctness and X-check
module multiply_sva #(
  parameter int din0_WIDTH = 1,
  parameter int din1_WIDTH = 1,
  parameter int dout_WIDTH = 1
)(
  input  logic                         clk,
  input  logic                         ce,
  input  logic signed [din0_WIDTH-1:0] a,
  input  logic signed [din1_WIDTH-1:0] b,
  input  logic signed [2*dout_WIDTH-1:0] p
);
  function automatic logic signed [2*dout_WIDTH-1:0]
    trunc_prod(input logic signed [din0_WIDTH-1:0] a_i,
               input logic signed [din1_WIDTH-1:0] b_i);
    trunc_prod = $signed(a_i) * $signed(b_i);
  endfunction

  default clocking cb @(posedge clk); endclocking

  assert property ( $signed(p) == trunc_prod(a,b) )
    else $error("multiply.p != truncated product");

  assert property ( !$isunknown({a,b}) |-> !$isunknown(p) )
    else $error("X on p when inputs known");
endmodule

bind multiply
  multiply_sva #(
    .din0_WIDTH(din0_WIDTH),
    .din1_WIDTH(din1_WIDTH),
    .dout_WIDTH(dout_WIDTH)
  ) multiply_sva_i (.*);