module two_bit_sat_counter_sva (
    input logic CLK,
    input logic [1:0] count_i,
    input logic       op,
    input logic [1:0] count
);

    // 00 with op=0 increments to 01.
    check_00_when_op0_increments: assert property (
        @(posedge CLK) (count_i == 2'b00) && (op == 1'b0) |-> (count == 2'b01)
    );

    // 00 with op=1 saturates (holds at 00).
    check_00_when_op1_saturates: assert property (
        @(posedge CLK) (count_i == 2'b00) && (op == 1'b1) |-> (count == 2'b00)
    );

    // 01 with op=0 increments to 10.
    check_01_when_op0_increments: assert property (
        @(posedge CLK) (count_i == 2'b01) && (op == 1'b0) |-> (count == 2'b10)
    );

    // 01 with op=1 decrements to 00.
    check_01_when_op1_decrements: assert property (
        @(posedge CLK) (count_i == 2'b01) && (op == 1'b1) |-> (count == 2'b00)
    );

    // 10 with op=0 decrements to 01.
    check_10_when_op0_decrements: assert property (
        @(posedge CLK) (count_i == 2'b10) && (op == 1'b0) |-> (count == 2'b01)
    );

    // 10 with op=1 increments to 11.
    check_10_when_op1_increments: assert property (
        @(posedge CLK) (count_i == 2'b10) && (op == 1'b1) |-> (count == 2'b11)
    );

    // 11 with op=0 decrements to 10.
    check_11_when_op0_decrements: assert property (
        @(posedge CLK) (count_i == 2'b11) && (op == 1'b0) |-> (count == 2'b10)
    );

    // 11 with op=1 saturates (holds at 11).
    check_11_when_op1_saturates: assert property (
        @(posedge CLK) (count_i == 2'b11) && (op == 1'b1) |-> (count == 2'b11)
    );

    // For mid values (01,10) output always differs from input.
    check_mid_values_always_change: assert property (
        @(posedge CLK) (count_i inside {2'b01,2'b10}) |-> (count != count_i)
    );

    // Output is either equal or +/-1 from input (no multi-step or wrap beyond 1).
    check_output_step_or_hold_valid: assert property (
        @(posedge CLK) 1'b1 |-> ( (count == count_i) || (count == (count_i + 2'b01)) || (count == (count_i - 2'b01)) )
    );

    // Holding output equals input only at bounds (00 or 11) with op=1.
    check_hold_only_at_bounds_with_op1: assert property (
        @(posedge CLK) (count == count_i) |-> ((count_i inside {2'b00,2'b11}) && (op == 1'b1))
    );

endmodule