// SVA for dff_module and top_module

// Assertions bound to each dff_module instance
module dff_module_sva (input clk, input d, input q);

  // On each falling edge, q must update to the sampled d (post-NBA)
  property p_capture;
    @(negedge clk) ##0 (q == $sampled(d));
  endproperty
  a_capture: assert property(p_capture);

  // Inputs/outputs must be known at capture/update
  a_d_known: assert property(@(negedge clk) !$isunknown(d));
  a_q_known: assert property(@(negedge clk) ##0 !$isunknown(q));

  // Q must only change on falling clock edges
  a_q_changes_only_on_fall: assert property(@(posedge q or negedge q) $fell(clk));

  // Coverage: observe both transitions and both captured values
  c_q_rise: cover property(@(negedge clk) ##0 $rose(q));
  c_q_fall: cover property(@(negedge clk) ##0 $fell(q));
  c_cap0:   cover property(@(negedge clk) (d==1'b0) ##0 (q==1'b0));
  c_cap1:   cover property(@(negedge clk) (d==1'b1) ##0 (q==1'b1));

endmodule

bind dff_module dff_module_sva u_dff_module_sva (.clk(clk), .d(d), .q(q));


// Bus-level assertions/coverage for top_module
module top_module_sva (input clk, input [7:0] d, input [7:0] q, input [7:0] q_internal);

  // Connectivity: q must mirror q_internal
  a_bus_connect: assert property(@(posedge clk or negedge clk) q == q_internal);

  // Bus-level coverage: capture all-zeros and all-ones
  c_all_zero: cover property(@(negedge clk) (d==8'h00) ##0 (q==8'h00));
  c_all_ones: cover property(@(negedge clk) (d==8'hFF) ##0 (q==8'hFF));

endmodule

bind top_module top_module_sva u_top_module_sva (.clk(clk), .d(d), .q(q), .q_internal(q_internal));