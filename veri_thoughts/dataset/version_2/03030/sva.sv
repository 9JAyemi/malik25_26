module adder_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic Cin,
    input logic [7:0] S,
    input logic Cout
);

    // No RTL clock/reset; sample this combinational adder on an external clock.

    // Combined outputs must equal the 9-bit addition of A, B, and Cin.
    check_full_sum: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Sum bits must match the low 8 bits of the arithmetic result.
    check_sum_low_bits: assert property (
        @(posedge clk) S == (({1'b0, A} + {1'b0, B} + Cin)[7:0])
    );

    // Carry-out must match the top bit of the arithmetic result.
    check_carry_out: assert property (
        @(posedge clk) Cout == (({1'b0, A} + {1'b0, B} + Cin)[8])
    );

    // The least-significant sum bit must implement full-adder parity.
    check_lsb_parity: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Stable inputs must produce stable outputs across samples.
    check_stable_inputs_hold_outputs: assert property (
        @(posedge clk) $stable({A, B, Cin}) |-> $stable({Cout, S})
    );

    // Output changes must be caused by an input change across samples.
    check_output_change_requires_input_change: assert property (
        @(posedge clk) !$stable({Cout, S}) |-> !$stable({A, B, Cin})
    );

endmodule