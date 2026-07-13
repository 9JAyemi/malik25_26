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

    // Reset clears the registered outputs.
    check_reset_clears_outputs: assert property (
        @(posedge clk) rst |=> (control_o == 9'b0 && pc_op == 2'b00)
    );

    // When enabled, en_mem is captured into control_o[0].
    check_en_captures_en_mem: assert property (
        @(posedge clk) disable iff (rst) en |=> (control_o[0] == $past(en_mem))
    );

    // When enabled, should_branch is captured into control_o[1].
    check_en_captures_should_branch: assert property (
        @(posedge clk) disable iff (rst) en |=> (control_o[1] == $past(should_branch))
    );

    // When enabled, imm is captured into control_o[2].
    check_en_captures_imm: assert property (
        @(posedge clk) disable iff (rst) en |=> (control_o[2] == $past(imm))
    );

    // When enabled, pc_op selects 2'b10 for imm=1.
    check_en_selects_and_when_imm: assert property (
        @(posedge clk) disable iff (rst) (en && imm) |=> (pc_op == 2'b10)
    );

    // When enabled, pc_op selects 2'b00 for imm=0.
    check_en_selects_add_when_not_imm: assert property (
        @(posedge clk) disable iff (rst) (en && !imm) |=> (pc_op == 2'b00)
    );

    // When not enabled, control_o holds its previous value.
    check_hold_control_when_disabled: assert property (
        @(posedge clk) disable iff (rst) !en |=> (control_o == $past(control_o))
    );

    // When not enabled, pc_op holds its previous value.
    check_hold_pc_op_when_disabled: assert property (
        @(posedge clk) disable iff (rst) !en |=> (pc_op == $past(pc_op))
    );

endmodule