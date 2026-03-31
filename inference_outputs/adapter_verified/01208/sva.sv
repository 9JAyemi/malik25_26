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

// Reset clears both outputs on the next clock.
    check_reset_clears_outputs: assert property (
        @(posedge clk) rst |=> (control_o == 9'b0) && (pc_op == 2'b00)
    );

// When enabled, control_o[0] captures en_mem.
    check_control_en_mem_capture: assert property (
        @(posedge clk) disable iff (rst) en |=> (control_o[0] == $past(en_mem))
    );

// When enabled, control_o[1] captures should_branch.
    check_control_branch_capture: assert property (
        @(posedge clk) disable iff (rst) en |=> (control_o[1] == $past(should_branch))
    );

// When enabled, control_o[2] captures imm.
    check_control_imm_capture: assert property (
        @(posedge clk) disable iff (rst) en |=> (control_o[2] == $past(imm))
    );

// When enabled with imm high, pc_op selects 2'b10.
    check_pc_op_and_when_imm_high: assert property (
        @(posedge clk) disable iff (rst) (en && imm) |=> (pc_op == 2'b10)
    );

// When enabled with imm low, pc_op selects 2'b00.
    check_pc_op_add_when_imm_low: assert property (
        @(posedge clk) disable iff (rst) (en && !imm) |=> (pc_op == 2'b00)
    );

// When not enabled, control_o holds its previous value.
    check_control_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst) !en |=> (control_o == $past(control_o))
    );

// When not enabled, pc_op holds its previous value.
    check_pc_op_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst) !en |=> (pc_op == $past(pc_op))
    );

endmodule
