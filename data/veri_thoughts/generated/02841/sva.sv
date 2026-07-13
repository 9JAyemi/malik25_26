module latch_id_ex_sva (
    input logic             clock,
    input logic             reset,
    input logic      [ 5:0] stall,
    input logic      [31:0] id_instruction,
    input logic      [31:0] ex_instruction,
    input logic      [ 7:0] id_operator,
    input logic      [ 7:0] ex_operator,
    input logic      [ 2:0] id_category,
    input logic      [ 2:0] ex_category,
    input logic      [31:0] id_operand_a,
    input logic      [31:0] ex_operand_a,
    input logic      [31:0] id_operand_b,
    input logic      [31:0] ex_operand_b,
    input logic             id_register_write_enable,
    input logic             ex_register_write_enable,
    input logic      [ 4:0] id_register_write_address,
    input logic      [ 4:0] ex_register_write_address,
    input logic      [31:0] id_register_write_data,
    input logic      [31:0] ex_register_write_data
);

    // Synchronous reset drives all EX pipeline registers to zero on the next cycle.
    reset_clears_ex: assert property (
        @(posedge clock)
            reset |=> (ex_instruction == 32'b0) &&
                     (ex_operator == 8'h0) &&
                     (ex_category == 3'b000) &&
                     (ex_operand_a == 32'b0) &&
                     (ex_operand_b == 32'b0) &&
                     (ex_register_write_enable == 1'b0) &&
                     (ex_register_write_address == 5'b0) &&
                     (ex_register_write_data == 32'b0)
    );

    // Bubble/flush when stall[2]==1 && stall[3]==0 inserts zeros on the next cycle.
    bubble_inserts_zeros: assert property (
        @(posedge clock) disable iff (reset)
            (stall[2] == 1'b1 && stall[3] == 1'b0) |=> (ex_instruction == 32'b0) &&
                                                     (ex_operator == 8'h0) &&
                                                     (ex_category == 3'b000) &&
                                                     (ex_operand_a == 32'b0) &&
                                                     (ex_operand_b == 32'b0) &&
                                                     (ex_register_write_enable == 1'b0) &&
                                                     (ex_register_write_address == 5'b0) &&
                                                     (ex_register_write_data == 32'b0)
    );

    // When not stalled (stall[2]==0), instruction/operator/category propagate to EX next cycle.
    propagate_instr_ops: assert property (
        @(posedge clock) disable iff (reset)
            (stall[2] == 1'b0) |=> (ex_instruction == $past(id_instruction)) &&
                                  (ex_operator == $past(id_operator)) &&
                                  (ex_category == $past(id_category))
    );

    // When not stalled (stall[2]==0), operands propagate to EX next cycle.
    propagate_operands: assert property (
        @(posedge clock) disable iff (reset)
            (stall[2] == 1'b0) |=> (ex_operand_a == $past(id_operand_a)) &&
                                  (ex_operand_b == $past(id_operand_b))
    );

    // When not stalled (stall[2]==0), writeback controls/data propagate to EX next cycle.
    propagate_writeback: assert property (
        @(posedge clock) disable iff (reset)
            (stall[2] == 1'b0) |=> (ex_register_write_enable == $past(id_register_write_enable)) &&
                                  (ex_register_write_address == $past(id_register_write_address)) &&
                                  (ex_register_write_data == $past(id_register_write_data))
    );

    // When fully stalled (stall[2]==1 && stall[3]==1), all EX registers hold their value.
    hold_on_full_stall: assert property (
        @(posedge clock) disable iff (reset)
            (stall[2] == 1'b1 && stall[3] == 1'b1) |=> (ex_instruction == $past(ex_instruction)) &&
                                                      (ex_operator == $past(ex_operator)) &&
                                                      (ex_category == $past(ex_category)) &&
                                                      (ex_operand_a == $past(ex_operand_a)) &&
                                                      (ex_operand_b == $past(ex_operand_b)) &&
                                                      (ex_register_write_enable == $past(ex_register_write_enable)) &&
                                                      (ex_register_write_address == $past(ex_register_write_address)) &&
                                                      (ex_register_write_data == $past(ex_register_write_data))
    );

    // Any change of EX registers must be caused by prior reset, flush, or load (stall[2]==0).
    ex_change_has_valid_cause: assert property (
        @(posedge clock) disable iff (reset)
            ((ex_instruction != $past(ex_instruction)) ||
             (ex_operator != $past(ex_operator)) ||
             (ex_category != $past(ex_category)) ||
             (ex_operand_a != $past(ex_operand_a)) ||
             (ex_operand_b != $past(ex_operand_b)) ||
             (ex_register_write_enable != $past(ex_register_write_enable)) ||
             (ex_register_write_address != $past(ex_register_write_address)) ||
             (ex_register_write_data != $past(ex_register_write_data)))
            |-> ($past(reset) ||
                 ($past(stall[2]) == 1'b1 && $past(stall[3]) == 1'b0) ||
                 ($past(stall[2]) == 1'b0))
    );

    // If a flush was taken last cycle and this cycle is a hold, EX remains zero.
    zeros_persist_after_flush_then_hold: assert property (
        @(posedge clock) disable iff (reset)
            ($past(stall[2]) == 1'b1 && $past(stall[3]) == 1'b0 && (stall[2] == 1'b1 && stall[3] == 1'b1))
            |-> (ex_instruction == 32'b0) &&
                (ex_operator == 8'h0) &&
                (ex_category == 3'b000) &&
                (ex_operand_a == 32'b0) &&
                (ex_operand_b == 32'b0) &&
                (ex_register_write_enable == 1'b0) &&
                (ex_register_write_address == 5'b0) &&
                (ex_register_write_data == 32'b0)
    );

endmodule