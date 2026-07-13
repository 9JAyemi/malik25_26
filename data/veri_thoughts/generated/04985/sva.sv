module latch_EX_MEM_sva (
    input logic clk,
    input logic reset,
    input logic ena,
    input logic [31:0] alu_result_in,
    input logic [31:0] r_data2_in,
    input logic [4:0] mux_RegDst_in,
    input logic wb_RegWrite_in,
    input logic wb_MemtoReg_in,
    input logic m_MemWrite_in,
    input logic [5:0] opcode_in,
    input logic [31:0] alu_result_out,
    input logic [31:0] r_data2_out,
    input logic [4:0] mux_RegDst_out,
    input logic wb_RegWrite_out,
    input logic wb_MemtoReg_out,
    input logic m_MemWrite_out,
    input logic [5:0] opcode_out
);

    // Reset clears all latched outputs on the next cycle.
    check_reset_clears_outputs: assert property (
        @(posedge clk)
        reset |=> ((alu_result_out == 32'd0) &&
                   (r_data2_out == 32'd0) &&
                   (mux_RegDst_out == 5'd0) &&
                   (wb_RegWrite_out == 1'b0) &&
                   (wb_MemtoReg_out == 1'b0) &&
                   (m_MemWrite_out == 1'b0) &&
                   (opcode_out == 6'd0))
    );

    // Enable captures alu_result_in.
    check_capture_alu_result: assert property (
        @(posedge clk) disable iff (reset)
        ena |=> (alu_result_out == $past(alu_result_in))
    );

    // Enable captures r_data2_in.
    check_capture_r_data2: assert property (
        @(posedge clk) disable iff (reset)
        ena |=> (r_data2_out == $past(r_data2_in))
    );

    // Enable captures mux_RegDst_in.
    check_capture_mux_regdst: assert property (
        @(posedge clk) disable iff (reset)
        ena |=> (mux_RegDst_out == $past(mux_RegDst_in))
    );

    // Enable captures wb_RegWrite_in.
    check_capture_wb_regwrite: assert property (
        @(posedge clk) disable iff (reset)
        ena |=> (wb_RegWrite_out == $past(wb_RegWrite_in))
    );

    // Enable captures wb_MemtoReg_in.
    check_capture_wb_memtoreg: assert property (
        @(posedge clk) disable iff (reset)
        ena |=> (wb_MemtoReg_out == $past(wb_MemtoReg_in))
    );

    // Enable captures m_MemWrite_in.
    check_capture_m_memwrite: assert property (
        @(posedge clk) disable iff (reset)
        ena |=> (m_MemWrite_out == $past(m_MemWrite_in))
    );

    // Enable captures opcode_in.
    check_capture_opcode: assert property (
        @(posedge clk) disable iff (reset)
        ena |=> (opcode_out == $past(opcode_in))
    );

    // When enable is low, all outputs hold their values.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !ena |=> ($stable(alu_result_out) &&
                  $stable(r_data2_out) &&
                  $stable(mux_RegDst_out) &&
                  $stable(wb_RegWrite_out) &&
                  $stable(wb_MemtoReg_out) &&
                  $stable(m_MemWrite_out) &&
                  $stable(opcode_out))
    );

    // Output changes only follow a prior reset or enabled capture.
    check_output_change_requires_prev_update: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate &&
         ($changed(alu_result_out) ||
          $changed(r_data2_out) ||
          $changed(mux_RegDst_out) ||
          $changed(wb_RegWrite_out) ||
          $changed(wb_MemtoReg_out) ||
          $changed(m_MemWrite_out) ||
          $changed(opcode_out)))
        |-> $past(reset || ena)
    );

endmodule