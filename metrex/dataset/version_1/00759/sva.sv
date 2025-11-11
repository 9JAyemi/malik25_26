// SVA checker for counter
module counter_sva (
  input logic        clk,
  input logic        reset,   // async, active-high
  input logic        enable,
  input logic [3:0]  count
);

  default clocking cb @(posedge clk); endclocking

  // Basic sanity: no X/Z on key signals at clock edge
  a_no_xz:        assert property (!$isunknown({reset, enable, count}));

  // Async reset must drive count to 0 immediately (after NBA update)
  a_async_rst_0:  assert property (@(posedge reset) ##0 (count == 4'd0));

  // While reset is high at a clock edge, count must be 0
  a_sync_rst_0:   assert property (reset |-> ##0 (count == 4'd0));

  // Next-state function when not in or just leaving reset:
  // count_next = count_prev + (enable ? 1 : 0) modulo 16
  a_next_state:   assert property (
                    (!reset && !$past(reset,1,1'b0))
                    |-> count == (($past(count) + ($past(enable) ? 4'd1 : 4'd0)) & 4'hF)
                  );

  // Coverage
  c_inc:          cover  property (
                    (!reset && !$past(reset,1,1'b0) && $past(enable))
                    |=> count == (($past(count)+4'd1) & 4'hF)
                  );

  c_hold:         cover  property (
                    (!reset && !$past(reset,1,1'b0) && !$past(enable))
                    |=> count == $past(count)
                  );

  c_wrap:         cover  property (
                    (!reset && !$past(reset,1,1'b0) && $past(enable) && $past(count)==4'hF)
                    |=> count == 4'h0
                  );

  c_async_rst:    cover  property (@(posedge reset) ##0 (count == 4'd0));

endmodule

// Bind into DUT
bind counter counter_sva counter_sva_i (.*);