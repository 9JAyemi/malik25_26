// SVA for up_down_counter
// Bind into each DUT instance to access internals (count_reg1/2).

bind up_down_counter up_down_counter_sva u_up_down_counter_sva();

module up_down_counter_sva;

  // Access DUT scope signals directly via bind
  // signals: clk, up_down, load, count, count_reg1, count_reg2

  default clocking cb @(posedge clk); endclocking
  default disable iff (1'b0);

  // Basic sanity: no X/Z on key signals at sample points
  a_no_x: assert property (!$isunknown({load, up_down, count_reg1, count_reg2, count}))
    else $error("X/Z detected on control/state");

  // Synchronous load clears the pipeline registers
  a_load_clears: assert property (load |=> (count_reg1 == 3'd0 && count_reg2 == 3'd0))
    else $error("load did not clear regs to 0");

  // Pipeline update when not loading
  a_pipe_update: assert property (!load |=> (count_reg1 == $past(count_reg2) && count_reg2 == $past(count)))
    else $error("pipeline update mismatch (reg1/reg2)");

  // Combinational function: count must always reflect reg1 +/- 1
  // Immediate assertion to check continuously (not just at clk)
  always_comb begin
    assert (count === (up_down ? (count_reg1 + 3'd1) : (count_reg1 - 3'd1)))
      else $error("count != f(count_reg1, up_down)");
  end

  // End-to-end functional relation over two cycles (no load in both)
  // count(now) = f(count(two_clocks_ago), up_down(now))
  a_e2e_2cycle: assert property (!load && !$past(load) |-> 
                                 count == (up_down ? ($past(count,2) + 3'd1) : ($past(count,2) - 3'd1)))
    else $error("2-cycle end-to-end relation failed");

  // Coverage
  c_load:        cover property (load);
  c_dir_up:      cover property (up_down);
  c_dir_down:    cover property (!up_down);
  c_dir_toggle:  cover property ($past(up_down) != up_down);

  // Wrap-around coverage (requires two consecutive non-load cycles)
  c_wrap_up:   cover property (!load && !$past(load) && $past(count,2) == 3'd7 && up_down && count == 3'd0);
  c_wrap_down: cover property (!load && !$past(load) && $past(count,2) == 3'd0 && !up_down && count == 3'd7);

endmodule