// SVA for counter: concise, high-quality checks + coverage
// Bind this module to the DUT.
module counter_sva(
  input clk,
  input rst,
  input en,
  input up_down,
  input [3:0] out
);
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset checks
  ap_async_reset_immediate: assert property (@(negedge rst) out == 4'h0);
  ap_in_reset_zero:        assert property ( !rst |-> (out == 4'h0) );
  ap_in_reset_hold:        assert property ( !rst && $past(!rst) |-> $stable(out) );

  // Hold when disabled
  ap_hold_when_disabled: assert property ( rst && $past(rst) && !en |-> out == $past(out) );

  // Up-count behavior
  ap_up_step:  assert property ( rst && $past(rst) && en && up_down && $past(out) != 4'hF
                                 |-> out == $past(out) + 4'd1 );
  ap_up_wrap:  assert property ( rst && $past(rst) && en && up_down && $past(out) == 4'hF
                                 |-> out == 4'h0 );

  // Down-count behavior
  ap_down_step: assert property ( rst && $past(rst) && en && !up_down && $past(out) != 4'h0
                                  |-> out == $past(out) - 4'd1 );
  ap_down_wrap: assert property ( rst && $past(rst) && en && !up_down && $past(out) == 4'h0
                                  |-> out == 4'hF );

  // Functional coverage
  cp_reset_assert:   cover property (@(negedge rst) 1'b1);
  cp_reset_release:  cover property ($rose(rst));
  cp_hold_disabled:  cover property ( rst && $past(rst) && !en ##1 out == $past(out) );
  cp_up_step:        cover property ( rst && $past(rst) && en && up_down && $past(out) != 4'hF
                                      ##1 out == $past(out) + 4'd1 );
  cp_up_wrap:        cover property ( rst && $past(rst) && en && up_down && $past(out) == 4'hF
                                      ##1 out == 4'h0 );
  cp_down_step:      cover property ( rst && $past(rst) && en && !up_down && $past(out) != 4'h0
                                      ##1 out == $past(out) - 4'd1 );
  cp_down_wrap:      cover property ( rst && $past(rst) && en && !up_down && $past(out) == 4'h0
                                      ##1 out == 4'hF );

endmodule

bind counter counter_sva u_counter_sva (
  .clk(clk),
  .rst(rst),
  .en(en),
  .up_down(up_down),
  .out(out)
);