module control_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic en_mem,
    input logic mem_wait,
    input logic should_branch,
    input logic imm,
    input logic [8:0] control_o,
    input logic [1:0] pc_op
);
    // Reset drives outputs to zero on the next cycle.
    reset_clears_outputs: assert property (
        @(posedge clk) rst |=> (control_o == 9'b0) && (pc_op == 2'b00)
    );

    // When en is LOW, outputs hold their previous values.
    hold_when_en_low: assert property (
        @(posedge clk) disable iff (rst) !en |=> (control_o == $past(control_o)) && (pc_op == $past(pc_op))
    );

    // When en is HIGH, control_o[0] captures en_mem.
    control0_captures_en_mem: assert property (
        @(posedge clk) disable iff (rst) en |=> (control_o[0] == $past(en_mem))
    );

    // When en is HIGH, control_o[1] captures should_branch.
    control1_captures_should_branch: assert property (
        @(posedge clk) disable iff (rst) en |=> (control_o[1] == $past(should_branch))
    );

    // When en is HIGH, control_o[2] captures imm.
    control2_captures_imm: assert property (
        @(posedge clk) disable iff (rst) en |=> (control_o[2] == $past(imm))
    );

    // When en is HIGH and imm is HIGH, pc_op captures 2'b10.
    pc_op_captures_10_on_imm: assert property (
        @(posedge clk) disable iff (rst) (en && imm) |=> (pc_op == 2'b10)
    );

    // When en is HIGH and imm is LOW, pc_op captures 2'b00.
    pc_op_captures_00_on_no_imm: assert property (
        @(posedge clk) disable iff (rst) (en && !imm) |=> (pc_op == 2'b00)
    );

    // pc_op can only be 2'b00 or 2'b10 when en is HIGH.
    pc_op_legal_values_when_en: assert property (
        @(posedge clk) disable iff (rst) en |=> ((pc_op == 2'b00) || (pc_op == 2'b10))
    );

    // pc_op changes only if en is HIGH in the previous cycle.
    pc_op_change_requires_prev_en: assert property (
        @(posedge clk) disable iff (rst) $changed(pc_op) |-> $past(en)
    );

    // control_o changes only if en is HIGH in the previous cycle.
    control_o_change_requires_prev_en: assert property (
        @(posedge clk) disable iff (rst) $changed(control_o) |-> $past(en)
    );
endmodule