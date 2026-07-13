module MEM_WB_sva (
    input logic clk,
    input logic [1:0]  control_wb_in,
    input logic [31:0] Read_data_in,
    input logic [31:0] ALU_result_in,
    input logic [4:0]  Write_reg_in,
    input logic [1:0]  mem_control_wb,
    input logic [31:0] Read_data,
    input logic [31:0] mem_ALU_result,
    input logic [4:0]  mem_Write_reg
);
    // mem_control_wb captures control_wb_in with 1-cycle latency.
    capture_mem_control_wb: assert property (
        @(posedge clk) mem_control_wb == $past(control_wb_in)
    );

    // Read_data captures Read_data_in with 1-cycle latency.
    capture_Read_data: assert property (
        @(posedge clk) Read_data == $past(Read_data_in)
    );

    // mem_ALU_result captures ALU_result_in with 1-cycle latency.
    capture_mem_ALU_result: assert property (
        @(posedge clk) mem_ALU_result == $past(ALU_result_in)
    );

    // mem_Write_reg captures Write_reg_in with 1-cycle latency.
    capture_mem_Write_reg: assert property (
        @(posedge clk) mem_Write_reg == $past(Write_reg_in)
    );

    // If control_wb_in is stable this cycle, mem_control_wb is stable next cycle.
    stable_propagation_mem_control_wb: assert property (
        @(posedge clk) $stable(control_wb_in) |=> $stable(mem_control_wb)
    );

    // If Read_data_in is stable this cycle, Read_data is stable next cycle.
    stable_propagation_Read_data: assert property (
        @(posedge clk) $stable(Read_data_in) |=> $stable(Read_data)
    );

    // If ALU_result_in is stable this cycle, mem_ALU_result is stable next cycle.
    stable_propagation_mem_ALU_result: assert property (
        @(posedge clk) $stable(ALU_result_in) |=> $stable(mem_ALU_result)
    );

    // If Write_reg_in is stable this cycle, mem_Write_reg is stable next cycle.
    stable_propagation_mem_Write_reg: assert property (
        @(posedge clk) $stable(Write_reg_in) |=> $stable(mem_Write_reg)
    );

    // If control_wb_in changes this cycle, mem_control_wb changes next cycle.
    change_propagation_mem_control_wb: assert property (
        @(posedge clk) $changed(control_wb_in) |=> $changed(mem_control_wb)
    );

    // If Read_data_in changes this cycle, Read_data changes next cycle.
    change_propagation_Read_data: assert property (
        @(posedge clk) $changed(Read_data_in) |=> $changed(Read_data)
    );

    // If ALU_result_in changes this cycle, mem_ALU_result changes next cycle.
    change_propagation_mem_ALU_result: assert property (
        @(posedge clk) $changed(ALU_result_in) |=> $changed(mem_ALU_result)
    );

    // If Write_reg_in changes this cycle, mem_Write_reg changes next cycle.
    change_propagation_mem_Write_reg: assert property (
        @(posedge clk) $changed(Write_reg_in) |=> $changed(mem_Write_reg)
    );
endmodule