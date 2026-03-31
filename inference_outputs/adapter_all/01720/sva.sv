module axi_timer_sva
   #(parameter INIT_VALUE = 16'h1000)
   (input logic [4:0] bus2ip_addr_i_reg,
    input logic Q,
    input logic ce_expnd_i_5);

  wire [3:0] lut_input;
  assign lut_input = {bus2ip_addr_i_reg[2], Q, bus2ip_addr_i_reg[1:0]};

  // Address 0x1000 maps to ce_expnd_i_5 low.
  check_addr_1000_low: assert property (
    @($global_clock) (lut_input == 4'b0000) |-> (ce_expnd_i_5 == 1'b0)
  );

  // Address 0x1001 maps to ce_expnd_i_5 low.
  check_addr_1001_low: assert property (
    @($global_clock) (lut_input == 4'b0001) |-> (ce_expnd_i_5 == 1'b0)
  );

  // Address 0x1002 maps to ce_expnd_i_5 low.
  check_addr_1002_low: assert property (
    @($global_clock) (lut_input == 4'b0010) |-> (ce_expnd_i_5 == 1'b0)
  );

  // Address 0x1003 maps to ce_expnd_i_5 low.
  check_addr_1003_low: assert property (
    @($global_clock) (lut_input == 4'b0011) |-> (ce_expnd_i_5 == 1'b0)
  );

  // Address 0x1004 maps to ce_expnd_i_5 low.
  check_addr_1004_low: assert property (
    @($global_clock) (lut_input == 4'b0100) |-> (ce_expnd_i_5 == 1'b0)
  );

  // Address 0x1005 maps to ce_expnd_i_5 low.
  check_addr_1005_low: assert property (
    @($global_clock) (lut_input == 4'b0101) |-> (ce_expnd_i_5 == 1'b0)
  );

  // Address 0x1006 maps to ce_expnd_i_5 low.
  check_addr_1006_low: assert property (
    @($global_clock) (lut_input == 4'b0110) |-> (ce_expnd_i_5 == 1'b0)
  );

  // Address 0x1007 maps to ce_expnd_i_5 low.
  check_addr_1007_low: assert property (
    @($global_clock) (lut_input == 4'b0111) |-> (ce_expnd_i_5 == 1'b0)
  );

  // Address 0x1008 maps to ce_expnd_i_5 high.
  check_addr_1008_high: assert property (
    @($global_clock) (lut_input == 4'b1000) |-> (ce_expnd_i_5 == 1'b1)
  );

  // Address 0x1009 maps to ce_expnd_i_5 low.
  check_addr_1009_low: assert property (
    @($global_clock) (lut_input == 4'b1001) |-> (ce_expnd_i_5 == 1'b0)
  );

  // Address 0x100A maps to ce_expnd_i_5 low.
  check_addr_100a_low: assert property (
    @($global_clock) (lut_input == 4'b1010) |-> (ce_expnd_i_5 == 1'b0)
  );

  // Address 0x100B maps to ce_expnd_i_5 low.
  check_addr_100b_low: assert property (
    @($global_clock) (lut_input == 4'b1011) |-> (ce_expnd_i_5 == 1'b0)
  );

  // Address 0x100C maps to ce_expnd_i_5 low.
  check_addr_100c_low: assert property (
    @($global_clock) (lut_input == 4'b1100) |-> (ce_expnd_i_5 == 1'b0)
  );

  // Address 0x100D maps to ce_expnd_i_5 low.
  check_addr_100d_low: assert property (
    @($global_clock) (lut_input == 4'b1101) |-> (ce_expnd_i_5 == 1'b0)
  );

  // Address 0x100E maps to ce_expnd_i_5 low.
  check_addr_100e_low: assert property (
    @($global_clock) (lut_input == 4'b1110) |-> (ce_expnd_i_5 == 1'b0)
  );

  // Address 0x100F maps to ce_expnd_i_5 low.
  check_addr_100f_low: assert property (
    @($global_clock) (lut_input == 4'b1111) |-> (ce_expnd_i_5 == 1'b0)
  );

endmodule