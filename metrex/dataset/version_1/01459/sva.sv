// -----------------------------------------------------------------------------
// SVA for div and div_top
// -----------------------------------------------------------------------------

// Assertions bound into 'div'
module div_sva #(
  parameter int in0_WIDTH = 32,
  parameter int in1_WIDTH = 32,
  parameter int out_WIDTH = 32
)(
  input  logic                       clk,
  input  logic                       reset,
  input  logic                       ce,
  input  logic [in0_WIDTH-1:0]       dividend,
  input  logic [in1_WIDTH-1:0]       divisor,
  input  logic [out_WIDTH-1:0]       quot,
  input  logic [out_WIDTH-1:0]       remd,
  // internals
  input  logic [in0_WIDTH-1:0]       temp_dividend,
  input  logic [in1_WIDTH-1:0]       temp_divisor,
  input  logic [out_WIDTH-1:0]       temp_quot,
  input  logic [out_WIDTH-1:0]       temp_remd
);
  default clocking cb @ (posedge clk); endclocking
  default disable iff (reset);

  function automatic [out_WIDTH-1:0] exp_quot(input [in0_WIDTH-1:0] a, input [in1_WIDTH-1:0] b);
    exp_quot = (b == '0) ? '0 : (a / b);
  endfunction
  function automatic [out_WIDTH-1:0] exp_remd(input [in0_WIDTH-1:0] a, input [in1_WIDTH-1:0] b);
    exp_remd = (b == '0) ? a[out_WIDTH-1:0] : (a % b);
  endfunction

  // Outputs reflect temps
  assert property (quot == temp_quot && remd == temp_remd);

  // Hold when ce==0
  assert property (!ce |=> {temp_dividend,temp_divisor,temp_quot,temp_remd,quot,remd}
                          == $past({temp_dividend,temp_divisor,temp_quot,temp_remd,quot,remd}));

  // Capture of inputs on ce
  assert property ($past(ce) |-> (temp_dividend == $past(dividend) &&
                                  temp_divisor  == $past(divisor)));

  // Functional correctness on consecutive ce cycles (1-cycle latency)
  assert property ($past(ce) && ce |-> (quot == exp_quot($past(dividend), $past(divisor)) &&
                                        remd == exp_remd($past(dividend), $past(divisor))));

  // Remainder range when divisor != 0
  assert property ($past(ce) && ce && $past(divisor) != '0 |-> remd < $past(divisor));

  // Outputs only change on ce (excluding reset)
  assert property ((quot != $past(quot) || remd != $past(remd)) |-> $past(ce));

  // Knownness
  assert property (!$isunknown({quot, remd, temp_dividend, temp_divisor, temp_quot, temp_remd}));

  // Reset clears next cycle
  assert property (@(posedge clk) disable iff (1'b0)
                   reset |=> (temp_dividend=='0 && temp_divisor=='0 &&
                              temp_quot=='0 && temp_remd=='0 &&
                              quot=='0 && remd=='0));

  // Coverage
  cover property ($past(ce) && ce && $past(divisor) != '0);
  cover property ($past(ce) && ce && $past(divisor) == '0);
  cover property (!ce ##1 ce);
  cover property (@(posedge clk) disable iff (1'b0) reset ##1 !reset);
endmodule

bind div div_sva #(
  .in0_WIDTH(in0_WIDTH),
  .in1_WIDTH(in1_WIDTH),
  .out_WIDTH(out_WIDTH)
) u_div_sva (
  .clk(clk),
  .reset(reset),
  .ce(ce),
  .dividend(dividend),
  .divisor(divisor),
  .quot(quot),
  .remd(remd),
  .temp_dividend(temp_dividend),
  .temp_divisor(temp_divisor),
  .temp_quot(temp_quot),
  .temp_remd(temp_remd)
);

// Assertions bound into 'div_top' (interface-level checks)
module div_top_sva #(
  parameter int din0_WIDTH = 1,
  parameter int din1_WIDTH = 1,
  parameter int dout_WIDTH = 1
)(
  input  logic                   clk,
  input  logic                   reset,
  input  logic                   ce,
  input  logic [din0_WIDTH-1:0]  din0,
  input  logic [din1_WIDTH-1:0]  din1,
  input  logic [dout_WIDTH-1:0]  dout,
  input  logic [dout_WIDTH-1:0]  sig_remd
);
  default clocking cb @ (posedge clk); endclocking
  default disable iff (reset);

  function automatic [dout_WIDTH-1:0] t_exp_quot(input [din0_WIDTH-1:0] a, input [din1_WIDTH-1:0] b);
    t_exp_quot = (b == '0) ? '0 : (a / b);
  endfunction
  function automatic [dout_WIDTH-1:0] t_exp_remd(input [din0_WIDTH-1:0] a, input [din1_WIDTH-1:0] b);
    t_exp_remd = (b == '0) ? a[dout_WIDTH-1:0] : (a % b);
  endfunction

  // No X/Z on top-level outputs
  assert property (!$isunknown({dout, sig_remd}));

  // Top-level outputs hold when ce==0
  assert property (!ce |=> {dout, sig_remd} == $past({dout, sig_remd}));

  // Functional correctness across wrapper on consecutive ce
  assert property ($past(ce) && ce |-> (dout == t_exp_quot($past(din0), $past(din1)) &&
                                        sig_remd == t_exp_remd($past(din0), $past(din1))));

  // Reset clears next cycle
  assert property (@(posedge clk) disable iff (1'b0)
                   reset |=> (dout=='0 && sig_remd=='0));

  // Coverage
  cover property ($past(ce) && ce && $past(din1) != '0);
  cover property ($past(ce) && ce && $past(din1) == '0);
endmodule

bind div_top div_top_sva #(
  .din0_WIDTH(din0_WIDTH),
  .din1_WIDTH(din1_WIDTH),
  .dout_WIDTH(dout_WIDTH)
) u_div_top_sva (
  .clk(clk),
  .reset(reset),
  .ce(ce),
  .din0(din0),
  .din1(din1),
  .dout(dout),
  .sig_remd(sig_remd)
);