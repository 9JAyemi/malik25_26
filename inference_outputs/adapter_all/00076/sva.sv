module top_module_sva (
    input logic [3:0]  A,
    input logic [1:0]  shift_amount,
    input logic        shift_dir,
    input logic        enable,
    input logic [1:0]  select,
    input logic [15:0] out
);

    // No RTL clock or reset; sample combinational behavior on the global clock.

    // Left shift by 0 passes A through unchanged.
    check_left_shift_by_0: assert property (
        @($global_clock)
        (shift_dir && (shift_amount == 2'b00)) |-> (out == {12'b0, A})
    );

    // Left shift by 1 inserts a zero into bit 0.
    check_left_shift_by_1: assert property (
        @($global_clock)
        (shift_dir && (shift_amount == 2'b01)) |-> (out == {11'b0, A[2:0], 1'b0})
    );

    // Left shift by 2 inserts zeros into bits 1:0.
    check_left_shift_by_2: assert property (
        @($global_clock)
        (shift_dir && (shift_amount == 2'b10)) |-> (out == {9'b0, A[1:0], 2'b00})
    );

    // Left shift by 3 inserts zeros into bits 2:0.
    check_left_shift_by_3: assert property (
        @($global_clock)
        (shift_dir && (shift_amount == 2'b11)) |-> (out == {6'b0, A[0], 3'b000})
    );

    // Right shift by 0 passes A through unchanged.
    check_right_shift_by_0: assert property (
        @($global_clock)
        (!shift_dir && (shift_amount == 2'b00)) |-> (out == {12'b0, A})
    );

    // Right shift by 1 inserts a zero into bit 3.
    check_right_shift_by_1: assert property (
        @($global_clock)
        (!shift_dir && (shift_amount == 2'b01)) |-> (out == {12'b0, 1'b0, A[3:1]})
    );

    // Right shift by 2 inserts zeros into bits 3:2.
    check_right_shift_by_2: assert property (
        @($global_clock)
        (!shift_dir && (shift_amount == 2'b10)) |-> (out == {10'b0, 2'b00, A[3:2]})
    );

    // Right shift by 3 inserts zeros into bits 3:0.
    check_right_shift_by_3: assert property (
        @($global_clock)
        (!shift_dir && (shift_amount == 2'b11)) |-> (out == {7'b0, 3'b000, A[3]})
    );

    // With enable low, the decoder contribution is zero.
    check_decoder_disabled_zero: assert property (
        @($global_clock)
        !enable |-> (out == {12'b0, A})
    );

    // With enable high and select 00, the decoder contribution is 0001.
    check_decoder_select_00: assert property (
        @($global_clock)
        (enable && (select == 2'b00)) |-> (out == {12'b0, 12'b0, 1'b1})
    );

    // With enable high and select 01, the decoder contribution is 0010.
    check_decoder_select_01: assert property (
        @($global_clock)
        (enable && (select == 2'b01)) |-> (out == {12'b0, 13'b0, 1'b1})
    );

    // With enable high and select 10, the decoder contribution is 0100.
    check_decoder_select_10: assert property (
        @($global_clock)
        (enable && (select == 2'b10)) |-> (out == {12'b0, 14'b0, 2'b10})
    );

    // With enable high and select 11, the decoder contribution is 1000.
    check_decoder_select_11: assert property (
        @($global_clock)
        (enable && (select == 2'b11)) |-> (out == {12'b0, 15'b0, 3'b100})
    );

endmodule