// SVA for fixed_point_arithmetic (bindable, concise, high-quality)
module fixed_point_arithmetic_sva #(
  parameter int n = 16,
  parameter int int_bits = 8
) (
  input  logic                 clk,
  input  logic                 rst_n,
  input  logic [n-1:0]         a,
  input  logic [n-1:0]         b,
  input  logic [1:0]           op,
  input  logic [n-1:0]         c
);

  localparam int               frac_bits = n - int_bits;
  localparam logic [n-1:0]     SC       = logic'(1) << frac_bits;
  localparam logic [n-1:0]     MAXV     = logic'( (1 << (n-1)) - 1 );

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Helpers (match DUT truncation semantics)
  function automatic logic [n-1:0] mul_scale(input logic [n-1:0] x, y);
    logic [2*n-1:0] prod;
    prod = x * y;
    mul_scale = (prod / SC)[n-1:0];
  endfunction

  function automatic logic [n-1:0] div_scale_q(input logic [n-1:0] x, y);
    logic [2*n-1:0] num;
    num = x * SC;
    div_scale_q = (num / y)[n-1:0];
  endfunction

  // No X on outputs
  assert property ($stable(c) or !$isunknown(c)));

  // Core functional checks (combinational, same-cycle)
  assert property (op==2'b00 |-> ##0 c == (a + b));                          // add
  assert property (op==2'b01 |-> ##0 c == (a - b));                          // sub (mod 2^n)
  assert property (op==2'b10 |-> ##0 c == mul_scale(a,b));                   // mul scaled
  assert property (op==2'b11 && b==0 |-> ##0 c == MAXV);                     // div by zero -> MAXV
  assert property (op==2'b11 && b!=0 |-> ##0 c == div_scale_q(a,b));         // div scaled

  // Division semantics (Euclidean remainder bounds when b!=0)
  assert property (op==2'b11 && b!=0 |-> ##0
    begin
      logic [2*n-1:0] num, qext, bext, rem;
      num  = a * SC;
      qext = {{n{1'b0}}, c};
      bext = {{n{1'b0}}, b};
      rem  = num - qext*bext;
      (rem < bext)
    end);

  // Useful corner-case assertions (also serve as lightweight checks)
  assert property (op==2'b00 && b==0 |-> ##0 c==a);
  assert property (op==2'b01 && b==0 |-> ##0 c==a);
  assert property (op==2'b01 && a==b |-> ##0 c=='0);
  assert property (op==2'b10 && (a=='0 || b=='0) |-> ##0 c=='0);
  assert property (op==2'b10 && b==SC |-> ##0 c==a);
  assert property (op==2'b11 && b==SC |-> ##0 c==a);

  // Coverage: op modes, div-by-zero path, overflow/underflow events
  cover property (op==2'b00);
  cover property (op==2'b01);
  cover property (op==2'b10);
  cover property (op==2'b11);
  cover property (op==2'b11 && b==0);

  // Add overflow and sub underflow (unsigned wrap)
  cover property (op==2'b00 && ({1'b0,a}+{1'b0,b})[n]);       // add carry-out
  cover property (op==2'b01 && (a < b));                      // sub borrow

  // Mul/div quotient overflow (pre-truncation has MSBs beyond n)
  cover property (op==2'b10 && (((a*b)/SC) >> n) != '0);
  cover property (op==2'b11 && b!=0 && (((a*SC)/b) >> n) != '0);

endmodule

// Bind example (hook up clk/rst from your TB)
// bind fixed_point_arithmetic fixed_point_arithmetic_sva #(.n(n), .int_bits(8))
//   fixed_point_arithmetic_sva_i (.* , .clk(tb_clk), .rst_n(tb_rst_n));