module axi_timer_sva
   #(parameter INIT_VALUE = 16'h1000)
   (input logic [4:0] bus2ip_addr_i_reg,
    input logic Q,
    input logic ce_expnd_i_5);

  wire [3:0] lut_input;
  assign lut_input = {bus2ip_addr_i_reg[2], Q, bus2ip_addr_i_reg[1:0]};

  // ce_expnd_i_5 is low for all non-1000 input patterns.
  check_ce_low_for_non_1000: assert property (
    @($global_clock) (lut_input != 4'b1000) |-> (ce_expnd_i_5 == 1'b0)
  );

  // ce_expnd_i_5 is high only for the 1000 input pattern.
  check_ce_high_only_for_1000: assert property (
    @($global_clock) (lut_input == 4'b1000) |-> (ce_expnd_i_5 == 1'b1)
  );

  // ce_expnd_i_5 matches the implemented lookup table.
  check_ce_matches_lut: assert property (
    @($global_clock) ce_expnd_i_5 == (lut_input == 4'b1000)
  );

  // ce_expnd_i_5 is independent of bus2ip_addr_i_reg[3].
  check_ce_independent_of_addr_bit3: assert property (
    @($global_clock) ($changed(bus2ip_addr_i_reg[3])) ##1
    (lut_input == 4'b1000) |-> (ce_expnd_i_5 == 1'b1)
    ##1
    (lut_input != 4'b1000) |-> (ce_expnd_i_5 == 1'b0)
  );

  // ce_expnd_i_5 is independent of bus2ip_addr_i_reg[4].
  check_ce_independent_of_addr_bit4: assert property (
    @($global_clock) ($changed(bus2ip_addr_i_reg[4])) ##1
    (lut_input == 4'b1000) |-> (ce_expnd_i_5 == 1'b1)
    ##1
    (lut_input != 4'b1000) |-> (ce_expnd_i_5 == 1'b0)
  );

  // ce_expnd_i_5 is independent of Q when the address bits are stable.
  check_ce_independent_of_q: assert property (
    @($global_clock) ($changed(Q) && $stable(bus2ip_addr_i_reg)) ##1
    (lut_input == 4'b1000) |-> (ce_expnd_i_5 == 1'b1)
    ##1
    (lut_input != 4'b1000) |-> (ce_expnd_i_5 == 1'b0)
  );

endmodule