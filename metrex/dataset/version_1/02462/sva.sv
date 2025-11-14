// SVA for calculator
// Bind these assertions to the DUT (see bind statement at bottom).
module calculator_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [1:0]  op,
  input  logic [7:0]  in1,
  input  logic [7:0]  in2,
  input  logic [7:0]  out,
  input  logic        valid,
  input  logic [15:0] result
);

  // Expected 16-bit result per Verilog sizing rules
  function automatic logic [15:0] exp_result (logic [1:0] fop, logic [7:0] a, logic [7:0] b);
    case (fop)
      2'b00: exp_result = {8'h00, (a + b)};      // 8-bit add (wrap), zero-extend to 16
      2'b01: exp_result = {8'h00, (a - b)};      // 8-bit sub (wrap), zero-extend to 16
      2'b10: exp_result = (a * b);               // 16-bit mul
      2'b11: exp_result = {8'h00, (a / b)};      // 8-bit div (undefined if b==0)
      default: exp_result = 16'hxxxx;
    endcase
  endfunction

  // Asynchronous reset clears immediately after the reset edge (after NBA)
  property p_async_reset_clears;
    @(posedge reset) ##0 (result==16'h0 && out==8'h0 && valid==1'b0);
  endproperty
  assert property (p_async_reset_clears);

  // While reset is asserted at clk edge, outputs remain cleared (after NBA)
  property p_reset_holds_zero;
    @(posedge clk) reset |-> ##0 (result==16'h0 && out==8'h0 && valid==1'b0);
  endproperty
  assert property (p_reset_holds_zero);

  // valid must be 1 on every clock when not in reset (after NBA update)
  property p_valid_high_when_active;
    @(posedge clk) disable iff (reset) ##0 valid;
  endproperty
  assert property (p_valid_high_when_active);

  // Result update matches previous-cycle inputs/op (non-div-by-zero)
  property p_result_correct_nondiv0;
    @(posedge clk) disable iff (reset)
      !($past(op)==2'b11 && $past(in2)==8'h00)
      |-> ##0 (result == exp_result($past(op), $past(in1), $past(in2)));
  endproperty
  assert property (p_result_correct_nondiv0);

  // Division by zero drives unknown result
  property p_div_by_zero_unknown;
    @(posedge clk) disable iff (reset)
      ($past(op)==2'b11 && $past(in2)==8'h00)
      |-> ##0 $isunknown(result);
  endproperty
  assert property (p_div_by_zero_unknown);

  // out reflects low byte of previous result
  property p_out_matches_prev_result_lowbyte;
    @(posedge clk) disable iff (reset)
      $past(!reset) |-> ##0 (out == $past(result[7:0]));
  endproperty
  assert property (p_out_matches_prev_result_lowbyte);

  // Basic input sanity when active
  property p_inputs_known_when_active;
    @(posedge clk) disable iff (reset) !$isunknown({op,in1,in2});
  endproperty
  assert property (p_inputs_known_when_active);

  // Functional coverage
  cover property (@(posedge clk) !reset && op==2'b00);
  cover property (@(posedge clk) !reset && op==2'b01);
  cover property (@(posedge clk) !reset && op==2'b10);
  cover property (@(posedge clk) !reset && op==2'b11 && in2!=8'h00);
  cover property (@(posedge clk) !reset && op==2'b11 && in2==8'h00); // div by zero

  // Interesting corner cases
  cover property (@(posedge clk) !reset && op==2'b00 &&
                  ({1'b0,in1} + {1'b0,in2})[8]); // add overflow (wrap)
  cover property (@(posedge clk) !reset && op==2'b01 &&
                  (in1 < in2)); // sub underflow (wrap)
  cover property (@(posedge clk) !reset && op==2'b10 &&
                  ((in1*in2)[15:8] != 8'h00)); // mul high byte non-zero
endmodule

// Bind into DUT
bind calculator calculator_sva sva_i (
  .clk(clk),
  .reset(reset),
  .op(op),
  .in1(in1),
  .in2(in2),
  .out(out),
  .valid(valid),
  .result(result)
);