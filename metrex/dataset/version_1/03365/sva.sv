// SVA checker for Calculator
// Bind example (provide a sampling clock/reset from your TB):
// bind Calculator calc_sva u_calc_sva (.clk(tb_clk), .rst_n(tb_rst_n), .a(a), .b(b), .op(op), .result(result), .error(error));

module calc_sva (
  input  logic                clk,
  input  logic                rst_n,
  input  logic signed  [7:0]  a,
  input  logic signed  [7:0]  b,
  input  logic         [1:0]  op,
  input  logic         [7:0]  result,
  input  logic                error
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Reference model (bit-accurate to RTL, including truncations)
  function automatic logic signed [7:0] exp_res(input logic signed [7:0] a, b,
                                                input logic [1:0] op);
    automatic logic signed [15:0] t;
    case (op)
      2'b00: exp_res = a + b;
      2'b01: exp_res = a - b;
      2'b10: begin t = a * b; exp_res = t[7:0]; end
      2'b11: exp_res = (b == 0) ? 8'sh00 : (a / b);
      default: exp_res = 8'sh00;
    endcase
  endfunction

  // Correct signed overflow detection
  function automatic bit ovf_add(input logic signed [7:0] a, b,
                                 input logic signed [7:0] r);
    return (a[7] == b[7]) && (r[7] != a[7]);
  endfunction

  function automatic bit ovf_sub(input logic signed [7:0] a, b,
                                 input logic signed [7:0] r);
    return (a[7] != b[7]) && (r[7] != a[7]);
  endfunction

  function automatic bit exp_err(input logic signed [7:0] a, b,
                                 input logic [1:0] op,
                                 input logic signed [7:0] r);
    case (op)
      2'b00: exp_err = ovf_add(a,b,r);
      2'b01: exp_err = ovf_sub(a,b,r);
      2'b10: exp_err = 1'b0;
      2'b11: exp_err = (b == 0);
      default: exp_err = 1'b0;
    endcase
  endfunction

  // Sanity: no X/Z on interface
  assert property (!$isunknown({a,b,op})) else $error("Calculator inputs contain X/Z");
  assert property (!$isunknown({result,error})) else $error("Calculator outputs contain X/Z");

  // Main functional checks
  assert property (result == exp_res(a,b,op))
    else $error("Result mismatch: op=%0b a=%0d b=%0d got=%0d exp=%0d",
                op, a, b, $signed(result), exp_res(a,b,op));

  assert property (error == exp_err(a,b,op, $signed(result)))
    else $error("Error flag mismatch: op=%0b a=%0d b=%0d res=%0d got=%0b exp=%0b",
                op, a, b, $signed(result), error, exp_err(a,b,op,$signed(result)));

  // Targeted properties (redundant to main, but pinpoint issues)
  assert property (op==2'b11 && (b==0)  |-> error && result==8'h00);
  assert property (op==2'b11 && (b!=0) |-> !error && (result == (a / b)));
  assert property (op==2'b00 |-> error == ovf_add(a,b,$signed(result)));
  assert property (op==2'b01 |-> error == ovf_sub(a,b,$signed(result)));
  assert property (op==2'b10 |-> error == 1'b0); // catch latch/spurious error on multiply

  // Op encoding sanity when known
  assert property (!$isunknown(op) |-> op inside {2'b00,2'b01,2'b10,2'b11});

  // Coverage
  cover property (op==2'b00 &&  ovf_add(a,b,$signed(result)));
  cover property (op==2'b00 && !ovf_add(a,b,$signed(result)));
  cover property (op==2'b01 &&  ovf_sub(a,b,$signed(result)));
  cover property (op==2'b01 && !ovf_sub(a,b,$signed(result)));
  cover property (op==2'b10);
  cover property (op==2'b11 && b==0);
  cover property (op==2'b11 && b!=0);

endmodule