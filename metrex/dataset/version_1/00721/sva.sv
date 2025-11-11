// SVA for inverted_input_buffer
module inverted_input_buffer_sva(input logic i, ibar, o);

  // Sample on any relevant edge (combinational design, no clock)
  default clocking cb @(posedge i or negedge i or posedge ibar or negedge ibar or posedge o or negedge o); endclocking

  // Functional correctness
  a_inv: assert property (o === ~i);

  // ibar has no influence on o
  a_ibar_no_influence: assert property (@(posedge ibar or negedge ibar) $stable(i) |-> $stable(o));

  // If i is known, o must be known
  a_no_x_when_i_known: assert property (!$isunknown(i) |-> !$isunknown(o));

  // Any o toggle must be due to an i toggle
  a_o_change_implies_i_change: assert property (@(posedge o or negedge o) $changed(i));

  // Coverage
  c_i0: cover property (i==0 && o==1);
  c_i1: cover property (i==1 && o==0);
  c_i_rise: cover property ($rose(i) && o==0);
  c_i_fall: cover property ($fell(i) && o==1);
  c_ibar_toggle_stable: cover property (@(posedge ibar or negedge ibar) $stable(i) && $stable(o));
  c_i0_ibar0: cover property (i==0 && ibar==0);
  c_i0_ibar1: cover property (i==0 && ibar==1);
  c_i1_ibar0: cover property (i==1 && ibar==0);
  c_i1_ibar1: cover property (i==1 && ibar==1);

endmodule

bind inverted_input_buffer inverted_input_buffer_sva sva(.i(i), .ibar(ibar), .o(o));