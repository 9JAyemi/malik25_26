module INSTRUCTION_FETCH_STAGE_sva #(
    parameter ADDRESS_WIDTH = 32,
    parameter HIGH          = 1'b1,
    parameter LOW           = 1'b0
) (
    input logic                         CLK,
    input logic                         STALL_INSTRUCTION_FETCH_STAGE,
    input logic                         CLEAR_INSTRUCTION_FETCH_STAGE,
    input logic [ADDRESS_WIDTH-1:0]     PC_IN,
    input logic                         PC_VALID_IN,
    input logic [ADDRESS_WIDTH-1:0]     PC_OUT,
    input logic                         PC_VALID_OUT
);

    // Clear drives the stored PC to zero on the following cycle.
    check_clear_zeroes_pc: assert property (
        @(posedge CLK) disable iff (1'b0)
        (CLEAR_INSTRUCTION_FETCH_STAGE == HIGH) |=> (PC_OUT == {ADDRESS_WIDTH{1'b0}})
    );

    // Clear drives the stored valid bit low on the following cycle.
    check_clear_zeroes_valid: assert property (
        @(posedge CLK) disable iff (1'b0)
        (CLEAR_INSTRUCTION_FETCH_STAGE == HIGH) |=> (PC_VALID_OUT == LOW)
    );

    // When enabled, the stage captures the incoming PC.
    check_loads_pc_when_not_stalled: assert property (
        @(posedge CLK) disable iff (1'b0)
        (CLEAR_INSTRUCTION_FETCH_STAGE == LOW && STALL_INSTRUCTION_FETCH_STAGE == LOW)
        |=> (PC_OUT == $past(PC_IN))
    );

    // When enabled, the stage captures the incoming valid bit.
    check_loads_valid_when_not_stalled: assert property (
        @(posedge CLK) disable iff (1'b0)
        (CLEAR_INSTRUCTION_FETCH_STAGE == LOW && STALL_INSTRUCTION_FETCH_STAGE == LOW)
        |=> (PC_VALID_OUT == $past(PC_VALID_IN))
    );

    // When stalled without clear, the stored PC is held.
    check_stall_holds_pc: assert property (
        @(posedge CLK) disable iff (1'b0)
        (CLEAR_INSTRUCTION_FETCH_STAGE == LOW && STALL_INSTRUCTION_FETCH_STAGE == HIGH)
        |=> (PC_OUT == $past(PC_OUT))
    );

    // When stalled without clear, the stored valid bit is held.
    check_stall_holds_valid: assert property (
        @(posedge CLK) disable iff (1'b0)
        (CLEAR_INSTRUCTION_FETCH_STAGE == LOW && STALL_INSTRUCTION_FETCH_STAGE == HIGH)
        |=> (PC_VALID_OUT == $past(PC_VALID_OUT))
    );

    // Clear has priority over stall when both are asserted.
    check_clear_overrides_stall: assert property (
        @(posedge CLK) disable iff (1'b0)
        (CLEAR_INSTRUCTION_FETCH_STAGE == HIGH && STALL_INSTRUCTION_FETCH_STAGE == HIGH)
        |=> (PC_OUT == {ADDRESS_WIDTH{1'b0}} && PC_VALID_OUT == LOW)
    );

endmodule