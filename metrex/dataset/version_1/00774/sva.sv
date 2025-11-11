// SVA for MEM_WB: concise, high-quality checks and coverage

bind MEM_WB MEM_WB_sva mem_wb_sva_i(.*);

module MEM_WB_sva(
  input logic        clk,
  input logic [1:0]  control_wb_in,
  input logic [31:0] Read_data_in,
  input logic [31:0] ALU_result_in,
  input logic [4:0]  Write_reg_in,
  input logic [1:0]  mem_control_wb,
  input logic [31:0] Read_data,
  input logic [31:0] mem_ALU_result,
  input logic [4:0]  mem_Write_reg
);

  // Track first valid cycle for $past
  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  // 1-cycle pipeline capture
  property p_reg_capture;
    @(posedge clk)
      past_valid |->
      (mem_control_wb == $past(control_wb_in)) &&
      (Read_data      == $past(Read_data_in))  &&
      (mem_ALU_result == $past(ALU_result_in)) &&
      (mem_Write_reg  == $past(Write_reg_in));
  endproperty
  assert property (p_reg_capture);

  // No output glitches: output changes only on clk posedge
  property p_change_only_on_posedge;
    @($global_clock)
      ($changed(mem_control_wb) || $changed(Read_data) ||
       $changed(mem_ALU_result) || $changed(mem_Write_reg))
      |-> $rose(clk);
  endproperty
  assert property (p_change_only_on_posedge);

  // Clean inputs last cycle => clean outputs this cycle (no X/Z introduced)
  property p_no_x_from_clean_inputs;
    @(posedge clk)
      past_valid &&
      !$isunknown($past({control_wb_in, Read_data_in, ALU_result_in, Write_reg_in}))
      |->
      !$isunknown({mem_control_wb, Read_data, mem_ALU_result, mem_Write_reg});
  endproperty
  assert property (p_no_x_from_clean_inputs);

  // Power-up initialization to zero (per initial block intent)
  initial begin
    assert (mem_control_wb == 2'b00 &&
            Read_data      == 32'h0  &&
            mem_ALU_result == 32'h0  &&
            mem_Write_reg  == 5'h0)
      else $error("MEM_WB: outputs not initialized to zero at time 0");
  end

  // Coverage: updates happen and key values seen
  cover property (@(posedge clk) past_valid &&
                  ({mem_control_wb, Read_data, mem_ALU_result, mem_Write_reg} !=
                   $past({mem_control_wb, Read_data, mem_ALU_result, mem_Write_reg})));
  cover property (@(posedge clk) past_valid && mem_control_wb == 2'b00);
  cover property (@(posedge clk) past_valid && mem_control_wb == 2'b11);
  cover property (@(posedge clk) past_valid && mem_Write_reg  == 5'd0);
  cover property (@(posedge clk) past_valid && mem_Write_reg  == 5'd31);

endmodule