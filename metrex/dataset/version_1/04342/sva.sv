// SVA for up_down_counter
// Concise, high-quality checks + essential coverage

module up_down_counter_sva #(parameter int WIDTH = 4)
(
  input logic              clk,
  input logic              reset,
  input logic              enable,
  input logic              direction,
  input logic [WIDTH-1:0]  count
);

  default clocking cb @(posedge clk); endclocking

  // Helpers (guarantee WIDTH-sized wraparound math)
  function automatic [WIDTH-1:0] add1(input [WIDTH-1:0] v);
    add1 = v + {{(WIDTH-1){1'b0}},1'b1};
  endfunction
  function automatic [WIDTH-1:0] sub1(input [WIDTH-1:0] v);
    sub1 = v - {{(WIDTH-1){1'b0}},1'b1};
  endfunction

  // Past-valid guard
  bit pv;
  initial pv = 1'b0;
  always_ff @(posedge clk) pv <= 1'b1;

  // Sanity/X checks
  a_inputs_known:    assert property ( !$isunknown({reset, enable, direction}) );
  a_count_known:     assert property ( pv |-> !$isunknown(count) );

  // Next-state functional checks (synchronous semantics use $past)
  a_reset_dom:       assert property ( pv && $past(reset) |-> (count == '0) );

  a_hold_no_en:      assert property ( pv && !$past(reset) && !$past(enable)
                                       |-> (count == $past(count)) );

  a_inc:             assert property ( pv && !$past(reset) && $past(enable) && $past(direction)
                                       |-> (count == add1($past(count))) );

  a_dec:             assert property ( pv && !$past(reset) && $past(enable) && !$past(direction)
                                       |-> (count == sub1($past(count))) );

  // No spurious changes (only reset or enable may change count)
  a_change_cause:    assert property ( pv && (count != $past(count))
                                       |-> ($past(reset) || $past(enable)) );

  // Essential functional coverage
  c_reset_seen:      cover  property ( pv && $past(reset) && (count == '0) );

  c_hold_seen:       cover  property ( pv && !$past(reset) && !$past(enable)
                                       && (count == $past(count)) );

  c_inc_seen:        cover  property ( pv && !$past(reset) && $past(enable) && $past(direction)
                                       && (count == add1($past(count))) );

  c_dec_seen:        cover  property ( pv && !$past(reset) && $past(enable) && !$past(direction)
                                       && (count == sub1($past(count))) );

  c_wrap_up:         cover  property ( pv && !$past(reset) && $past(enable) && $past(direction)
                                       && ($past(count) == {WIDTH{1'b1}}) && (count == '0) );

  c_wrap_down:       cover  property ( pv && !$past(reset) && $past(enable) && !$past(direction)
                                       && ($past(count) == '0) && (count == {WIDTH{1'b1}}) );

endmodule

// Bind into DUT
bind up_down_counter up_down_counter_sva #(.WIDTH(4)) u_up_down_counter_sva (.*);