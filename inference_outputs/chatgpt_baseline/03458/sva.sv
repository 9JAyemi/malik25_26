module top_module_sva (
    input logic       a1,
    input logic       b1,
    input logic       a2,
    input logic       b2,
    input logic       select,
    input logic [1:0] sum
);

    // No clock or reset exists in the RTL; sample combinational behavior on the global clock.

    // Final sum must match the RTL expression exactly.
    check_sum_matches_rtl: assert property (
        @($global_clock)
        sum == ({(select ? (a2 & b2) : (a1 & b1)), (a1 ^ b1)} + {1'b0, (a2 ^ b2)})
    );

    // LSB is the XOR of the two adder sum bits.
    check_sum_lsb: assert property (
        @($global_clock)
        sum[0] == ((a1 ^ b1) ^ (a2 ^ b2))
    );

    // MSB is the selected carry plus the carry from the LSB addition.
    check_sum_msb: assert property (
        @($global_clock)
        sum[1] == ((select ? (a2 & b2) : (a1 & b1)) ^ ((a1 ^ b1) & (a2 ^ b2)))
    );

    // With select low, the upper bit source is the first adder carry.
    check_select_low_path: assert property (
        @($global_clock)
        !select |-> (sum == ({(a1 & b1), (a1 ^ b1)} + {1'b0, (a2 ^ b2)}))
    );

    // With select high, the upper bit source is the second adder carry.
    check_select_high_path: assert property (
        @($global_clock)
        select |-> (sum == ({(a2 & b2), (a1 ^ b1)} + {1'b0, (a2 ^ b2)}))
    );

    // If the second adder sum bit is zero, the final sum is the selected base vector.
    check_zero_second_addend: assert property (
        @($global_clock)
        ((a2 ^ b2) == 1'b0) |-> (sum == {(select ? (a2 & b2) : (a1 & b1)), (a1 ^ b1)})
    );

    // If the second adder sum bit is one, the final sum is the selected base vector plus one.
    check_one_second_addend: assert property (
        @($global_clock)
        ((a2 ^ b2) == 1'b1) |-> (sum == ({(select ? (a2 & b2) : (a1 & b1)), (a1 ^ b1)} + 2'b01))
    );

endmodule