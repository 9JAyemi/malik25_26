module two_bit_sat_counter_sva (
    input logic [1:0] count_i,
    input logic       op,
    input logic [1:0] count
);

    default clocking cb @($global_clock); endclocking

    // 00 with decrement holds at 00.
    check_from_00_dec: assert property (
        @($global_clock) (count_i == 2'b00 && op == 1'b0) |-> (count == 2'b00)
    );

    // 00 with increment moves to 01.
    check_from_00_inc: assert property (
        @($global_clock) (count_i == 2'b00 && op == 1'b1) |-> (count == 2'b01)
    );

    // 01 with decrement moves to 00.
    check_from_01_dec: assert property (
        @($global_clock) (count_i == 2'b01 && op == 1'b0) |-> (count == 2'b00)
    );

    // 01 with increment moves to 10.
    check_from_01_inc: assert property (
        @($global_clock) (count_i == 2'b01 && op == 1'b1) |-> (count == 2'b10)
    );

    // 10 with decrement moves to 01.
    check_from_10_dec: assert property (
        @($global_clock) (count_i == 2'b10 && op == 1'b0) |-> (count == 2'b01)
    );

    // 10 with increment saturates at 10.
    check_from_10_inc: assert property (
        @($global_clock) (count_i == 2'b10 && op == 1'b1) |-> (count == 2'b10)
    );

    // 11 with decrement moves to 10.
    check_from_11_dec: assert property (
        @($global_clock) (count_i == 2'b11 && op == 1'b0) |-> (count == 2'b10)
    );

    // 11 with increment holds at 11.
    check_from_11_inc: assert property (
        @($global_clock) (count_i == 2'b11 && op == 1'b1) |-> (count == 2'b11)
    );

endmodule