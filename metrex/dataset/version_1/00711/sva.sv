// SVA for MEM2WB: concise, full signal coverage, key checks and covers
module MEM2WB_sva (
    input clk, rst,
    input RegWrite_In,
    input [31:0] PC_In, ALUOut_In, rdata_In,
    input [4:0]  AddrC_In,
    input [1:0]  MemtoReg_In,
    input RegWrite_Out,
    input [31:0] PC_Out, ALUOut_Out, rdata_Out,
    input [4:0]  AddrC_Out,
    input [1:0]  MemtoReg_Out
);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  always @(posedge clk or posedge rst) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  // Bundle for concise checks
  wire [103:0] all_ins  = {RegWrite_In,  PC_In,  ALUOut_In,  rdata_In,  AddrC_In,  MemtoReg_In};
  wire [103:0] all_outs = {RegWrite_Out, PC_Out, ALUOut_Out, rdata_Out, AddrC_Out, MemtoReg_Out};

  // 1-cycle pipeline: outputs equal previous-cycle inputs when not in/coming from reset
  a_passthrough: assert property (disable iff (rst || !past_valid)
                                  all_outs == $past(all_ins));

  // While reset is asserted, outputs must be zero on every clk
  a_rst_zeros_clk: assert property (rst |-> (all_outs == '0));

  // Inputs must be known when captured; outputs must be known when observed
  a_no_x_in:  assert property (disable iff (rst) !$isunknown(all_ins));
  a_no_x_out: assert property (disable iff (rst || !past_valid) !$isunknown(all_outs));

  // If inputs are stable across cycles, outputs should be stable across cycles
  a_stable_when_inputs_stable: assert property (disable iff (rst || !past_valid)
                                               $stable(all_ins) |-> $stable(all_outs));

  // Optional immediate check at reset edge (asynchronous): ensure zeros after delta
  // Uses immediate assertion to observe after NBA
  always @(posedge rst) begin
    #0 assert (all_outs == '0)
      else $error("MEM2WB: outputs not zero immediately after async reset");
  end

  // Coverage
  c_reset_pulse:     cover property ($rose(rst));
  c_reset_release:   cover property ($fell(rst));
  c_pass_event:      cover property (disable iff (rst) $changed(all_ins) ##1 (all_outs == $past(all_ins)));
  c_memtoreg_00:     cover property (disable iff (rst) (MemtoReg_In == 2'b00) ##1 (MemtoReg_Out == 2'b00));
  c_memtoreg_01:     cover property (disable iff (rst) (MemtoReg_In == 2'b01) ##1 (MemtoReg_Out == 2'b01));
  c_memtoreg_10:     cover property (disable iff (rst) (MemtoReg_In == 2'b10) ##1 (MemtoReg_Out == 2'b10));
  c_memtoreg_11:     cover property (disable iff (rst) (MemtoReg_In == 2'b11) ##1 (MemtoReg_Out == 2'b11));
  c_regwrite_1:      cover property (disable iff (rst) RegWrite_In ##1 RegWrite_Out);
  c_regwrite_0:      cover property (disable iff (rst) !RegWrite_In ##1 !RegWrite_Out);

endmodule

// Bind into the DUT
bind MEM2WB MEM2WB_sva u_MEM2WB_sva (.*);