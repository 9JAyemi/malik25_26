module four_bit_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout,
    input logic [3:0] sum,
    input logic Cout1,
    input logic Cout2,
    input logic Cout3
);

    // No RTL clock or reset; assertions are sampled on $global_clock.

    // The output S must always mirror the internal sum bus.
    check_sum_output_alias: assert property (
        @($global_clock) S == sum
    );

    // Stage 0 sum matches full-adder XOR behavior.
    check_stage0_sum: assert property (
        @($global_clock) sum[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Stage 0 carry matches full-adder carry behavior.
    check_stage0_carry: assert property (
        @($global_clock) Cout1 == ((A[0] & B[0]) | (Cin & (A[0] ^ B[0])))
    );

    // Stage 1 sum uses Cout1 as its carry-in.
    check_stage1_sum: assert property (
        @($global_clock) sum[1] == (A[1] ^ B[1] ^ Cout1)
    );

    // Stage 1 carry matches full-adder carry behavior.
    check_stage1_carry: assert property (
        @($global_clock) Cout2 == ((A[1] & B[1]) | (Cout1 & (A[1] ^ B[1])))
    );

    // Stage 2 sum uses Cout2 as its carry-in.
    check_stage2_sum: assert property (
        @($global_clock) sum[2] == (A[2] ^ B[2] ^ Cout2)
    );

    // Stage 2 carry matches full-adder carry behavior.
    check_stage2_carry: assert property (
        @($global_clock) Cout3 == ((A[2] & B[2]) | (Cout2 & (A[2] ^ B[2])))
    );

    // Stage 3 sum uses Cout3 as its carry-in.
    check_stage3_sum: assert property (
        @($global_clock) sum[3] == (A[3] ^ B[3] ^ Cout3)
    );

    // Final carry-out matches the last full-adder stage.
    check_stage3_carry: assert property (
        @($global_clock) Cout == ((A[3] & B[3]) | (Cout3 & (A[3] ^ B[3])))
    );

    // The overall 5-bit result matches A + B + Cin.
    check_total_sum: assert property (
        @($global_clock) {Cout, S} == ({1'b0, A} + {1'b0, B} + {4'b0000, Cin})
    );

endmodule