module barrel_shifter_sva (
    input logic [3:0] in,
    input logic [1:0] shift_amt,
    input logic [3:0] out
);

    // When shift_amt is 00, out must equal in.
    check_shift_amt_00: assert property (
        @($global_clock) (shift_amt == 2'b00) |-> (out == in)
    );

    // When shift_amt is 01, out must match the RTL permutation.
    check_shift_amt_01: assert property (
        @($global_clock) (shift_amt == 2'b01) |-> (out == {in[3], in[0], in[1], in[2]})
    );

    // When shift_amt is 10, out must match the RTL permutation.
    check_shift_amt_10: assert property (
        @($global_clock) (shift_amt == 2'b10) |-> (out == {in[2], in[3], in[0], in[1]})
    );

    // When shift_amt is 11, out must match the RTL permutation.
    check_shift_amt_11: assert property (
        @($global_clock) (shift_amt == 2'b11) |-> (out == {in[1], in[2], in[3], in[0]})
    );

endmodule