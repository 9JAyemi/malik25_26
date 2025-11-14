// SVA for divider. Bind this module to the DUT.
module divider_sva (
  input logic         clk,
  input logic         rst,
  input logic         start,
  input logic [15:0]  dividend,
  input logic [15:0]  divisor,
  input logic [15:0]  quotient,
  input logic [15:0]  remainder,
  input logic         busy,
  input logic         valid,
  // internal state
  input logic [31:0]  dividend_temp,
  input logic [15:0]  divisor_temp,
  input logic [4:0]   count
);

  // Helper
  function automatic logic [31:0] zext16(input logic [15:0] x);
    return {16'd0, x};
  endfunction

  // Reset values when rst is high at a clock edge
  property p_reset_vals;
    @(posedge clk)
      rst |-> (quotient==0 && remainder==0 &&
               dividend_temp==0 && divisor_temp==0 &&
               count==0 && busy==0 && valid==0);
  endproperty
  assert property(p_reset_vals);

  // Start acceptance/load on next cycle
  property p_accept_loads;
    @(posedge clk) disable iff (rst)
      (start && !busy) |=> (busy && !valid &&
                            count==5'd16 &&
                            quotient==16'd0 &&
                            dividend_temp==zext16($past(dividend)) &&
                            divisor_temp==$past(divisor));
  endproperty
  assert property(p_accept_loads);

  // Busy duration exactly 16 cycles, then valid asserted and busy low
  property p_busy_len_then_valid;
    @(posedge clk) disable iff (rst)
      (start && !busy) |=> busy[*16] ##1 (valid && !busy);
  endproperty
  assert property(p_busy_len_then_valid);

  // Count bounds and monotonic progress while busy
  assert property (@(posedge clk) disable iff (rst) count<=5'd16);
  assert property (@(posedge clk) disable iff (rst)
                   ($past(busy) && $past(count)>0) |-> (count==$past(count)-1));

  // During busy, outputs behave
  assert property (@(posedge clk) disable iff (rst) busy |-> !valid);
  assert property (@(posedge clk) disable iff (rst) !(valid && busy));
  assert property (@(posedge clk) disable iff (rst) busy |-> (quotient==16'd0));
  assert property (@(posedge clk) disable iff (rst) busy |-> $stable(remainder));

  // Divisor stability requirements: input and latched copy must not change while busy
  assert property (@(posedge clk) disable iff (rst) busy |-> $stable(divisor));
  assert property (@(posedge clk) disable iff (rst) $past(busy) |-> (divisor_temp==$past(divisor_temp)));

  // Valid holds result stable until next accepted start
  assert property (@(posedge clk) disable iff (rst) (valid && !start) |-> $stable({valid, quotient, remainder}));

  // Functional correctness of final result (17 cycles after accept)
  property p_result_correct;
    @(posedge clk) disable iff (rst)
      (start && !busy) |=> ##17
        (valid &&
         (
           ($past(divisor,17)==16'd0) ?
             (quotient==16'hFFFF && remainder==$past(dividend,17)) :
             ( zext16($past(dividend,17)) == ($past(divisor,17)*quotient + zext16(remainder)) &&
               (remainder < $past(divisor,17)) )
         ));
  endproperty
  assert property(p_result_correct);

  // Optional: starting a new op while previous result is valid clears valid next cycle
  assert property (@(posedge clk) disable iff (rst) (start && valid) |=> !valid);

  // Coverage
  cover property (@(posedge clk) disable iff (rst) (start && !busy)); // any transaction
  cover property (@(posedge clk) disable iff (rst)
                  (start && !busy && divisor!=0) ##17 (valid && remainder==16'd0)); // exact division
  cover property (@(posedge clk) disable iff (rst)
                  (start && !busy && divisor!=0 && dividend<divisor) ##17 (valid && quotient==0 && remainder==$past(dividend,17)));
  cover property (@(posedge clk) disable iff (rst)
                  (start && !busy && dividend==0) ##17 (valid && quotient==0 && remainder==0));
  cover property (@(posedge clk) disable iff (rst)
                  (start && !busy && divisor==0) ##17 (valid && quotient==16'hFFFF && remainder==$past(dividend,17)));

endmodule

// Bind to DUT
bind divider divider_sva i_divider_sva (
  .clk(clk),
  .rst(rst),
  .start(start),
  .dividend(dividend),
  .divisor(divisor),
  .quotient(quotient),
  .remainder(remainder),
  .busy(busy),
  .valid(valid),
  .dividend_temp(dividend_temp),
  .divisor_temp(divisor_temp),
  .count(count)
);