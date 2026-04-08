module Adder_sva (
    input logic [19:0] Data_A_i,
    input logic [19:0] Data_B_i,
    input logic [20:0] O,
    input logic CO,
    input logic [3:0] S,
    input logic [3:0] DI
);

    // O is the 20-bit sum zero-extended to 21 bits.
    check_o_zero_extended_sum: assert property (
        @($global_clock) disable iff (1'b0)
        O == {1'b0, (Data_A_i + Data_B_i)}
    );

    // O[20] is always 0 because the sum is zero-extended.
    check_o_msb_zero: assert property (
        @($global_clock) disable iff (1'b0)
        O[20] == 1'b0
    );

    // CO follows the top bit of O.
    check_co_matches_o_msb: assert property (
        @($global_clock) disable iff (1'b0)
        CO == O[20]
    );

    // S is the low 4-bit sum of the inputs plus CO.
    check_s_low_nibble_sum: assert property (
        @($global_clock) disable iff (1'b0)
        S == (Data_A_i[3:0] + Data_B_i[3:0] + CO)
    );

    // DI packs CO with S[3:1].
    check_di_packing: assert property (
        @($global_clock) disable iff (1'b0)
        DI == {CO, S[3:1]}
    );

endmodule