// SVA for top_module. Focused, high-quality checks and coverage.
// Notes: Reset behaves as async active-low per RTL (negedge reset), despite comment.

module top_module_sva (
  input        clk,
  input        reset,      // active-low async per RTL
  input [2:0]  sel,
  input [3:0]  data,
  input        q,
  input [3:0]  mux_out,
  input        final_output,
  input [1:0]  count        // internal state, bound via bind
);

  // Sanity / X checks
  a_no_x_count:      assert property (@(posedge clk) !$isunknown(count));
  a_no_x_q:          assert property (@(posedge clk) !$isunknown(q));
  a_no_x_mux_out:    assert property (@(posedge clk) !$isunknown(mux_out));
  a_no_x_final:      assert property (@(posedge clk) !$isunknown(final_output));

  // Async active-low reset behavior
  a_reset_immediate_zero: assert property (@(negedge reset) ##0 (count==2'b00));
  a_hold_zero_while_reset:assert property (@(posedge clk) !reset |-> (count==2'b00));

  // State update: modulo-4 increment when out of reset
  a_count_incr_mod4: assert property (@(posedge clk)
                            reset |-> count == ($past(count,1, !reset, 2'b00) + 2'b01));

  // q mirrors MSB of count
  a_q_matches_count_msb: assert property (@(posedge clk) q == count[1]);

  // Mux: upper bits forced to 0; LSB equals selected data bit (sel[1:0])
  a_mux_shape:       assert property (@(posedge clk) mux_out == {3'b000, data[sel[1:0]]});

  // Mux independence from sel[2] (given sel[1:0] and data stable)
  a_sel2_irrelevant: assert property (@(posedge clk)
                            ($rose(sel[2]) || $fell(sel[2])) && $stable(sel[1:0]) && $stable(data)
                            |-> $stable(mux_out));

  // final_output functional check (combinational relation)
  a_final_function:  assert property (@(posedge clk) final_output == (count >= mux_out));

  // Strengthen final_output intent given mux_out can only be 0/1
  a_mux_out_upper_zero: assert property (@(posedge clk) mux_out[3:1]==3'b000);
  a_final_cases:        assert property (@(posedge clk)
                               (mux_out[0]==1'b0) -> final_output);
  a_final_case1:        assert property (@(posedge clk)
                               (mux_out[0]==1'b1) -> (final_output == (count!=2'b00)));

  // Coverage
  c_reset_cycle:   cover property (@(posedge clk) $fell(reset) ##1 $rose(reset));
  c_count_walk:    cover property (@(posedge clk) reset ##1 (count==2) ##1 (count==3) ##1 (count==0) ##1 (count==1));
  c_q_toggle_up:   cover property (@(posedge clk) $rose(q));
  c_q_toggle_down: cover property (@(posedge clk) $fell(q));
  c_mux0:          cover property (@(posedge clk) mux_out==4'b0000);
  c_mux1:          cover property (@(posedge clk) mux_out==4'b0001);
  c_final0:        cover property (@(posedge clk) final_output==1'b0);
  c_final1:        cover property (@(posedge clk) final_output==1'b1);

endmodule

// Bind into all instances of top_module
bind top_module top_module_sva i_top_module_sva (
  .clk(clk),
  .reset(reset),
  .sel(sel),
  .data(data),
  .q(q),
  .mux_out(mux_out),
  .final_output(final_output),
  .count(count) // internal
);