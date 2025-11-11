// SVA for binary_counter
module binary_counter_sva #(parameter WIDTH=16) (
  input logic              clk,
  input logic              reset,
  input logic [3:1]        ena,
  input logic [WIDTH-1:0]  q
);
  default clocking cb @(posedge clk); endclocking

  function automatic logic [WIDTH-1:0] inc_val(input logic [3:1] e);
    int inc;
    begin
      inc = 1 + (e[1]?2:0) + (e[2]?8:0) + (e[3]?16:0);
      inc_val = logic'(inc[WIDTH-1:0]);
    end
  endfunction

  // Basic sanity
  a_no_x:           assert property (!$isunknown({reset, ena, q})));
  a_reset_zero:     assert property (reset |-> q == '0);
  a_inc_rule:       assert property (!reset |-> q == $past(q) + inc_val(ena));
  a_q_changes_only: assert property (@(negedge clk) $stable(q));
  a_monotonic:      assert property (!reset |-> q != $past(q));

  // ena is module-driven constant in this DUT (due to truncation of 4'b0001 -> 3'b001)
  a_ena_const_val:  assert property (ena == 3'b001);
  a_ena_stable:     assert property ($stable(ena));

  // Coverage
  c_reset_pulse:    cover  property ($rose(reset));
  c_exit_reset:     cover  property ($fell(reset));
  c_increment:      cover  property (!reset && q == $past(q) + inc_val(ena));
  c_wraparound:     cover  property (!reset && (q < $past(q)));
endmodule

// Bind to DUT
bind binary_counter binary_counter_sva i_binary_counter_sva (
  .clk(clk),
  .reset(reset),
  .ena(ena),
  .q(q)
);