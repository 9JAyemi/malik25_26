// SVA bind module for jt12_dac2
module jt12_dac2_sva #(parameter int width=12)
(
  input  logic                       clk,
  input  logic                       rst,
  input  logic signed [width-1:0]    din,
  input  logic                       dout,
  input  logic        [width+5-1:0]  y,
  input  logic        [width+5-1:0]  error,
  input  logic        [width+5-1:0]  error_1,
  input  logic        [width+5-1:0]  error_2
);
  localparam int int_w = width+5;

  function automatic logic [width-1:0] f_undin(input logic signed [width-1:0] d);
    return {~d[width-1], d[width-2:0]};
  endfunction

  // Expected combinational values (match DUT sizing/truncation)
  logic [int_w:0]    y_exp_wide;
  logic [int_w-1:0]  y_exp, error_exp, scaled_dout;

  assign y_exp_wide  = {{(int_w+1-width){1'b0}}, f_undin(din)} + {error_1,1'b0} - {1'b0,error_2};
  assign y_exp       = y_exp_wide[int_w-1:0];
  assign scaled_dout = {{(int_w-(width+1)){1'b0}}, dout, {width{1'b0}}};
  assign error_exp   = y_exp - scaled_dout;

  // Sequential: reset clears state on next cycle
  assert property (@(posedge clk) rst |=> (error_1=='0 && error_2=='0));

  // Sequential: state updates when not in/just out of reset
  assert property (@(posedge clk) !rst && !$past(rst)
                   |=> (error_1==$past(error) && error_2==$past(error_1)));

  // Combinational core equations hold (sampled on clk)
  assert property (@(posedge clk)
                   !rst && !$isunknown({din,error_1,error_2})
                   |-> (y==y_exp && dout==~y[int_w-1] && error==error_exp));

  // No X on key signals in normal operation
  assert property (@(posedge clk) !rst && !$past(rst)
                   |-> !$isunknown({y,error,error_1,error_2,dout}));

  // Coverage
  cover property (@(posedge clk) rst ##1 !rst);                  // reset release
  cover property (@(posedge clk) !rst && dout==1'b0);
  cover property (@(posedge clk) !rst && dout==1'b1);
  cover property (@(posedge clk) !rst && $rose(dout));
  cover property (@(posedge clk) !rst && $fell(dout));

  localparam logic signed [width-1:0] S_MIN = {1'b1,{width-1{1'b0}}};
  localparam logic signed [width-1:0] S_MAX = {1'b0,{width-1{1'b1}}};
  cover property (@(posedge clk) !rst && din==S_MIN);
  cover property (@(posedge clk) !rst && din==S_MAX);
  cover property (@(posedge clk) !rst && din=='0);

endmodule

// Bind into DUT (tools allow binding to internal regs/wires by name)
bind jt12_dac2 jt12_dac2_sva #(.width(width)) jt12_dac2_sva_i
(
  .clk   (clk),
  .rst   (rst),
  .din   (din),
  .dout  (dout),
  .y     (y),
  .error (error),
  .error_1(error_1),
  .error_2(error_2)
);