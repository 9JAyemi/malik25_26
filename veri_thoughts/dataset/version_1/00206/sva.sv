// SVA for up_counter
module up_counter_sva #(parameter int SIZE=4)
(
  input logic              Clock,
  input logic              Reset,
  input logic              Enable,
  input logic              Load,
  input logic [SIZE-1:0]   Data,
  input logic [SIZE-1:0]   Q
);

  localparam logic [SIZE-1:0] MAX = {SIZE{1'b1}};

  default clocking cb @(posedge Clock); endclocking

  // Asynchronous reset checks (not disabled)
  a_async_reset_zero: assert property (@(posedge Reset) Q == '0);
  a_reset_hold_zero:  assert property (@(posedge Clock) Reset |-> Q == '0);
  a_no_x_rst:         assert property (@(posedge Reset) !$isunknown(Q));

  // Normal operation checks (ignore cycles with Reset=1)
  default disable iff (Reset);

  a_load:  assert property (Load |=> Q == $past(Data,1,Reset));
  a_inc:   assert property ((!Load && Enable) |=> Q == $past(Q,1,Reset) + 1);
  a_hold:  assert property ((!Load && !Enable) |=> Q == $past(Q,1,Reset));
  a_only_changes_on_ops: assert property ($changed(Q) |-> (Load || Enable));
  a_no_x_clk: assert property (!$isunknown(Q));

  // Coverage
  c_reset:  cover property (@(posedge Reset) Q=='0);
  c_load:   cover property (Load |=> Q == $past(Data,1,Reset));
  c_enable: cover property ((!Load && Enable) |=> Q == $past(Q,1,Reset)+1);
  c_hold:   cover property ((!Load && !Enable) |=> Q == $past(Q,1,Reset));
  c_wrap:   cover property ((!Load && Enable && $past(Q,1,Reset)==MAX) |=> Q=='0);
  c_both:   cover property ((Load && Enable) |=> Q == $past(Data,1,Reset));

endmodule

// Bind into DUT
bind up_counter up_counter_sva #(.SIZE(SIZE)) up_counter_sva_i (.*);