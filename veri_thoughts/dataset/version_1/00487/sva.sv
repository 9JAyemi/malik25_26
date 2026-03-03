// SVA for counter
module counter_sva(input logic clk, reset, up_down, input logic [3:0] out);
  default clocking cb @(posedge clk); endclocking

  // Sanity
  a_no_x_out:    assert property (! $isunknown(out));

  // Synchronous reset behavior
  a_reset_next:  assert property ($past(reset) |-> out == 4'h0);

  // Next-state correctness (up/down with wrap)
  a_up_next:     assert property ($past(!reset && up_down)
                                  |-> out == (($past(out)==4'hF) ? 4'h0 : $past(out)+1));
  a_down_next:   assert property ($past(!reset && !up_down)
                                  |-> out == (($past(out)==4'h0) ? 4'hF : $past(out)-1));

  // Counter changes every non-reset cycle when inputs known
  a_progress:    assert property ($past(!reset && !$isunknown(up_down) && !$isunknown(out))
                                  |-> out != $past(out));

  // Coverage
  c_reset:       cover property (reset ##1 out == 4'h0);
  c_up_wrap:     cover property ($past(!reset && up_down && $past(out)==4'hF) |-> out == 4'h0);
  c_down_wrap:   cover property ($past(!reset && !up_down && $past(out)==4'h0) |-> out == 4'hF);
  c_toggle_ud:   cover property ($past(!reset && up_down) && !up_down);
  c_toggle_du:   cover property ($past(!reset && !up_down) && up_down);
endmodule

bind counter counter_sva i_counter_sva (.*);