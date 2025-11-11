// SVA for accu — concise, high-quality checks and coverage
// Bind into DUT: bind accu accu_sva accu_sva_i(.*);

module accu_sva(
  input  logic         clk,
  input  logic         rst_n,
  input  logic [7:0]   data_in,
  input  logic         valid_a,
  input  logic         ready_b,
  input  logic         ready_a,
  input  logic         valid_b,
  input  logic [9:0]   data_out,
  input  logic [1:0]   count,   // internal
  input  logic [9:0]   acc      // internal
);

  default clocking cb @(posedge clk); endclocking
  // NOTE: do not disable all properties on reset; some check reset values.

  // Protocol assumption (environment): data only presented when ready
  assume property (cb (valid_a |-> ready_a));

  // Reset behavior (async active-low): regs must be 0 while in reset
  assert property (@(posedge clk) (!rst_n) |-> (count==2'b00 && acc==10'b0 && valid_b==1'b0));

  // Combinational ready mapping must hold every cycle
  assert property (cb ready_a == (~valid_b & ready_b));

  // Count updates: increment on valid_a, hold otherwise
  assert property (cb valid_a |=> ( ($past(count)==2'b00 && count==2'b01)
                                 || ($past(count)==2'b01 && count==2'b10)
                                 || ($past(count)==2'b10 && count==2'b11)
                                 || ($past(count)==2'b11 && count==2'b00) ));
  assert property (cb !valid_a |=> (count==$past(count)));

  // Accumulator updates: add data_in on valid_a, hold otherwise
  assert property (cb valid_a  |=> (acc == $past(acc) + $past(data_in)));
  assert property (cb !valid_a |=> (acc == $past(acc)));

  // valid_b next-state function (as implemented)
  assert property (cb (! $past(valid_a)) |-> (valid_b==1'b0)); // deassert when no input prev cycle
  assert property (cb ($past(valid_a) && $past(count)==2'b11) |-> valid_b); // assert after 4th

  // count relation when valid_b asserted (after 4th add, count wraps to 00)
  assert property (cb ($past(valid_a) && $past(count)==2'b11) |-> (valid_b && count==2'b00));

  // data_out update behavior (as implemented: uses old acc due to blocking assignment)
  assert property (cb (valid_a && count==2'b11) |=> (data_out == $past(acc)));
  // Intended functional check (should equal sum including last data_in) — will flag RTL bug
  assert property (cb (valid_a && count==2'b11) |=> (data_out == $past(acc) + $past(data_in)));

  // data_out holds its value otherwise
  assert property (cb !(valid_a && count==2'b11) |=> (data_out == $past(data_out)));

  // Sanity: data_out must be known when valid_b is asserted
  assert property (cb valid_b |-> !$isunknown(data_out));

  // Basic X/Z sanitation on handshake signals
  assert property (cb !$isunknown({ready_a, valid_b}));

  // ------------- Coverage -------------

  // Cover one full 4-beat accumulation block and output pulse
  sequence s_block4;
    (valid_a && count==2'b00) ##1
    (valid_a && count==2'b01) ##1
    (valid_a && count==2'b10) ##1
    (valid_a && count==2'b11);
  endsequence
  cover property (cb s_block4 ##1 (valid_b && count==2'b00));

  // Cover backpressure (ready_b stall then release)
  cover property (cb !ready_b ##1 ready_b);

  // Cover maximum-sum boundary case at output (4*255 = 1020)
  cover property (cb (valid_b && data_out==10'd1020));

  // Cover deassertion of valid_b when no input follows
  cover property (cb ($past(valid_a) && $past(count)==2'b11 && !valid_a) ##1 !valid_b);

endmodule

// Bind this SVA to the DUT
bind accu accu_sva accu_sva_i(.*);