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
    // Clock: clk (posedge). Reset: rst (active-high, synchronous). Logic is sequential (registered outputs).
    // Behavior: rst clears outputs; when en, control_o[2:0] reflect inputs and pc_op depends on imm; other bits hold.

    // Synchronous reset drives outputs to zero on the next cycle.
    reset_sync_clears_outputs: assert property (
        @(posedge clk) rst |=> (control_o == 9'b0) && (pc_op == 2'b00)
    );

    // When enabled, control_o[0] updates from en_mem on the next cycle.
    en_updates_control_o0: assert property (
        @(posedge clk) disable iff (rst) en |=> (control_o[0] == en_mem)
    );

    // When enabled, control_o[1] updates from should_branch on the next cycle.
    en_updates_control_o1: assert property (
        @(posedge clk) disable iff (rst) en |=> (control_o[1] == should_branch)
    );

    // When enabled, control_o[2] updates from imm on the next cycle.
    en_updates_control_o2: assert property (
        @(posedge clk) disable iff (rst) en |=> (control_o[2] == imm)
    );

    // When enabled, pc_op updates from imm on the next cycle.
    en_updates_pc_op_from_imm: assert property (
        @(posedge clk) disable iff (rst) en |=> (pc_op == (imm ? 2'b10 : 2'b00))
    );

    // When not enabled, control_o holds its previous value.
    hold_when_en_low_control: assert property (
        @(posedge clk) disable iff (rst) !en |=> (control_o == $past(control_o))
    );

    // When not enabled, pc_op holds its previous value.
    hold_when_en_low_pc: assert property (
        @(posedge clk) disable iff (rst) !en |=> (pc_op == $past(pc_op))
    );

    // When enabled, upper control bits [8:3] remain unchanged.
    hi_bits_unchanged_on_en: assert property (
        @(posedge clk) disable iff (rst) en |=> (control_o[8:3] == $past(control_o[8:3]))
    );

    // Low control bits [2:0] only change on cycles when en is high.
    control_lowbits_change_only_with_en: assert property (
        @(posedge clk) disable iff (rst) $changed(control_o[2:0]) |-> en
    );

    // pc_op only changes on cycles when en is high.
    pc_op_changes_only_with_en: assert property (
        @(posedge clk) disable iff (rst) $changed(pc_op) |-> en
    );

    // pc_op only takes values 2'b00 or 2'b10 when not in reset.
    pc_op_valid_values: assert property (
        @(posedge clk) disable iff (rst) (pc_op inside {2'b00, 2'b10})
    );

    // After an enable update, pc_op[1] matches control_o[2] (both from imm).
    pc_op_msb_matches_control2_on_update: assert property (
        @(posedge clk) disable iff (rst) en |=> (pc_op[1] == control_o[2])
    );
endmodule