// SVA checker for counter. Bind to the DUT for verification.
module counter_sva(
  input logic       clk,
  input logic       rst,
  input logic       up_down,
  input logic [7:0] out
);
  default clocking cb @(posedge clk); endclocking

  // Short-hands for previous-cycle values with safe defaults
  let prev_out = $past(out,      1, 8'd0);
  let prev_up  = $past(up_down,  1, 1'b0);
  let prev_rst = $past(rst,      1, 1'b0);
  let oper     = (!rst && !prev_rst);      // normal operation (not in or just after reset)

  // Reset behavior
  a_reset_next:  assert property (rst |=> out == 8'd0);
  a_reset_hold:  assert property (prev_rst && rst |-> out == 8'd0);
  a_no_x_oper:   assert property (!rst |-> (!$isunknown(out) && !$isunknown(up_down)));

  // First cycle after reset releases (prev out known 0)
  a_after_rst_up:   assert property (!rst && prev_rst &&  prev_up |-> out == 8'd1);
  a_after_rst_down: assert property (!rst && prev_rst && !prev_up |-> out == 8'd255);

  // Functional correctness (one-cycle next-state relation)
  a_up_inc:     assert property (oper &&  prev_up && (prev_out != 8'd255) |-> out == prev_out + 1);
  a_up_wrap:    assert property (oper &&  prev_up && (prev_out == 8'd255) |-> out == 8'd0);
  a_down_dec:   assert property (oper && !prev_up && (prev_out != 8'd0)   |-> out == prev_out - 1);
  a_down_wrap:  assert property (oper && !prev_up && (prev_out == 8'd0)   |-> out == 8'd255);

  // Progress: output must change every operational cycle
  a_progress:   assert property (oper |-> out != prev_out);

  // Coverage
  c_rst_cycle:      cover property (rst ##1 !rst);
  c_after_rst_up:   cover property (!rst && prev_rst &&  prev_up |-> out == 8'd1);
  c_after_rst_down: cover property (!rst && prev_rst && !prev_up |-> out == 8'd255);
  c_up_inc:         cover property (oper &&  prev_up && (prev_out != 8'd255) |-> out == prev_out + 1);
  c_up_wrap:        cover property (oper &&  prev_up && (prev_out == 8'd255) |-> out == 8'd0);
  c_down_dec:       cover property (oper && !prev_up && (prev_out != 8'd0)   |-> out == prev_out - 1);
  c_down_wrap:      cover property (oper && !prev_up && (prev_out == 8'd0)   |-> out == 8'd255);
endmodule

// Bind into the DUT
bind counter counter_sva u_counter_sva(.clk(clk), .rst(rst), .up_down(up_down), .out(out));