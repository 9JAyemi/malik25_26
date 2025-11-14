// SVA for nios_system_alu_carry_out
`ifndef NIOS_SYSTEM_ALU_CARRY_OUT_SVA
`define NIOS_SYSTEM_ALU_CARRY_OUT_SVA

module nios_system_alu_carry_out_sva (
  input logic        clk,
  input logic        reset_n,
  input logic [1:0]  address,
  input logic        in_port,
  input logic [31:0] readdata
);
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset: immediate zero and held during reset
  ap_async_reset_immediate: assert property (@(negedge reset_n) ##0 (readdata == 32'h0));
  ap_reset_hold:            assert property (!reset_n |-> (readdata == 32'h0));

  // No X/Z on key signals out of reset
  ap_no_x: assert property (disable iff (!reset_n)
                            !$isunknown({address, in_port, readdata}));

  // Functional behavior: zero-extended LSB muxed by address==0
  ap_value: assert property (disable iff (!reset_n)
                             readdata == {31'b0, ((address==2'b00) ? in_port : 1'b0)});

  // Structural guardrails: upper bits always zero; LSB matches function
  ap_upper_zeros: assert property (readdata[31:1] == '0);
  ap_lsb_func:    assert property (disable iff (!reset_n)
                                   readdata[0] == ((address==2'b00) ? in_port : 1'b0));

  // Coverage
  cv_reset_cycle:     cover property ($fell(reset_n) ##1 $rose(reset_n));
  cv_addr0_in1:       cover property (disable iff (!reset_n)
                                      (address==2'b00 && in_port && readdata==32'h1));
  cv_addr0_in0:       cover property (disable iff (!reset_n)
                                      (address==2'b00 && !in_port && readdata==32'h0));
  cv_addr_ne0_in1:    cover property (disable iff (!reset_n)
                                      (address!=2'b00 && in_port && readdata==32'h0));
  cv_readdata_0_1_0:  cover property (disable iff (!reset_n)
                                      (readdata==32'h0) ##1 (readdata==32'h1) ##1 (readdata==32'h0));
endmodule

bind nios_system_alu_carry_out nios_system_alu_carry_out_sva
(
  .clk(clk),
  .reset_n(reset_n),
  .address(address),
  .in_port(in_port),
  .readdata(readdata)
);

`endif