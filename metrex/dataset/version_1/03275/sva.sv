// SVA for Divider. Bind this to your instance/type.
// Provide a sampling clock/reset from your TB.

module Divider_sva #(parameter int n = 8)
(
  input  logic                 clk,
  input  logic                 rst_n,
  input  logic [n-1:0]         dividend,
  input  logic [n-1:0]         divisor,
  input  logic [n-1:0]         quotient,
  input  logic [n-1:0]         remainder
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  function automatic signed [n:0] sext(input logic [n-1:0] x);
    sext = {x[n-1], x};
  endfunction

  let DIVD = sext(dividend);
  let DIV  = sext(divisor);
  let QUO  = sext(quotient);
  let REM  = sext(remainder);
  let ABS_DIV = (DIV < 0) ? -DIV : DIV;
  let ABS_REM = (REM < 0) ? -REM : REM;
  let VALID   = (DIV != 0) && !$isunknown({dividend,divisor});

  // No-X on outputs when inputs are known and divisor!=0
  assert property (VALID |-> !$isunknown({quotient,remainder}))
    else $error("Divider: X/Z detected on outputs with valid inputs");

  // Illegal divide-by-zero detected
  assert property ((DIV == 0) |-> 1'b1)
    else $error("Divider: divide-by-zero");

  // If divide-by-zero occurs, outputs should go unknown (simulation)
  assert property ((DIV == 0) |-> ($isunknown(quotient) && $isunknown(remainder)))
    else $error("Divider: divisor==0 but outputs not X");

  // Mathematical identity: d = q*div + r
  assert property (VALID |-> (DIVD == (DIV*QUO + REM)))
    else $error("Divider: identity d = q*div + r violated");

  // Remainder magnitude constraint: |r| < |div|
  assert property (VALID |-> (ABS_REM < ABS_DIV))
    else $error("Divider: |remainder| not less than |divisor|");

  // Operator correctness (matches SystemVerilog / and %)
  assert property (VALID |-> (QUO == (DIVD / DIV)))
    else $error("Divider: quotient != dividend/divisor");
  assert property (VALID |-> (REM == (DIVD % DIV)))
    else $error("Divider: remainder != dividend%%divisor");

  // Sign rules
  assert property (VALID && (remainder != '0) |-> (remainder[n-1] == dividend[n-1]))
    else $error("Divider: remainder sign != dividend sign");
  assert property (VALID && (quotient  != '0) |-> (quotient[n-1]  == (dividend[n-1] ^ divisor[n-1])))
    else $error("Divider: quotient sign != dividend^divisor");

  // Coverage
  localparam logic [n-1:0] MAX_POS = {1'b0, {(n-1){1'b1}}};
  localparam logic [n-1:0] MIN_NEG = {1'b1, {(n-1){1'b0}}};

  cover property (DIV == 0); // divide-by-zero hit
  cover property (VALID && dividend[n-1]==0 && divisor[n-1]==0);
  cover property (VALID && dividend[n-1]==1 && divisor[n-1]==0);
  cover property (VALID && dividend[n-1]==0 && divisor[n-1]==1);
  cover property (VALID && dividend[n-1]==1 && divisor[n-1]==1);
  cover property (VALID && remainder=='0);
  cover property (VALID && divisor=={{(n-1){1'b0}},1'b1}); // +1
  cover property (VALID && divisor=={n{1'b1}});            // -1
  cover property (VALID && dividend==MIN_NEG && divisor=={{(n-1){1'b0}},1'b1});
  cover property (VALID && dividend==MIN_NEG && divisor=={n{1'b1}});
  cover property (VALID && dividend==MAX_POS && divisor=={{(n-1){1'b0}},1'b1});
  cover property (VALID && dividend==MAX_POS && divisor=={n{1'b1}});
  cover property (VALID && (divisor & (divisor - 1)) == '0 && divisor != '0); // power-of-two divisor

endmodule

// Example bind (edit clk/rst_n to your TB signals):
// bind Divider Divider_sva #(.n(n)) u_divider_sva ( .clk(tb_clk), .rst_n(tb_rst_n),
//   .dividend(dividend), .divisor(divisor), .quotient(quotient), .remainder(remainder) );