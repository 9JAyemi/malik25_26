// SVA for openhmc_counter48
module sva_openhmc_counter48 #(parameter DATASIZE=16) ();
  default clocking cb @(posedge clk); endclocking

  // Output mirrors internal register
  a_value_mirror: assert property (value == value_reg);

  // Reset behavior checked at clock edges (covers both sync/async implementations)
  a_reset_clear:  assert property (!res_n |-> (value_reg == '0 && load_enable_reg == 1'b0));

  // load_enable_reg is a 1-cycle delayed version of load_enable
  a_le_delay:     assert property (res_n && $past(res_n) |-> load_enable_reg == $past(load_enable));

  // State transitions based on {past(load_enable_reg), current increment}
  a_case_00_hold: assert property (res_n && $past(res_n) &&
                                   $past(load_enable_reg)==1'b0 && increment==1'b0
                                   |-> value_reg == $past(value_reg));

  a_case_01_inc:  assert property (res_n && $past(res_n) &&
                                   $past(load_enable_reg)==1'b0 && increment==1'b1
                                   |-> value_reg == $past(value_reg) + 1'b1);

  a_case_10_clr:  assert property (res_n && $past(res_n) &&
                                   $past(load_enable_reg)==1'b1 && increment==1'b0
                                   |-> value_reg == '0);

  a_case_11_one:  assert property (res_n && $past(res_n) &&
                                   $past(load_enable_reg)==1'b1 && increment==1'b1
                                   |-> value_reg == {{(DATASIZE-1){1'b0}},1'b1});

  // Functional coverage of all branches and wrap-around
  c_case_00: cover property (res_n && $past(res_n) &&
                             $past(load_enable_reg)==0 && increment==0 &&
                             value_reg == $past(value_reg));

  c_case_01: cover property (res_n && $past(res_n) &&
                             $past(load_enable_reg)==0 && increment==1 &&
                             value_reg == $past(value_reg)+1);

  c_case_10: cover property (res_n && $past(res_n) &&
                             $past(load_enable_reg)==1 && increment==0 &&
                             value_reg == '0);

  c_case_11: cover property (res_n && $past(res_n) &&
                             $past(load_enable_reg)==1 && increment==1 &&
                             value_reg == {{(DATASIZE-1){1'b0}},1'b1});

  c_wrap:    cover property (res_n && $past(res_n) &&
                             $past(load_enable_reg)==0 && increment==1 &&
                             $past(value_reg)=={DATASIZE{1'b1}} && value_reg=='0);

  c_reset_seq: cover property (!res_n ##1 res_n ##1 increment);
endmodule

bind openhmc_counter48 sva_openhmc_counter48 #(.DATASIZE(DATASIZE)) ();