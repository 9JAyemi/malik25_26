module binary_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic C_out
);

    // Combinational DUT sampled on an external clock; there is no reset in the RTL.

    // C_out is the carry bit of the 5-bit sum.
    check_cout_matches_sum_msb: assert property (
        @(posedge clk)
        C_out == (({1'b0, A} + {1'b0, B})[4])
    );

    // When the sum carries out, S matches the low 4 bits of the sum.
    check_sum_when_carry: assert property (
        @(posedge clk)
        (({1'b0, A} + {1'b0, B})[4]) |-> (S == (({1'b0, A} + {1'b0, B})[3:0]))
    );

    // When there is no carry, S is the low 3 bits zero-extended to 4 bits.
    check_sum_when_no_carry: assert property (
        @(posedge clk)
        !(({1'b0, A} + {1'b0, B})[4]) |-> (S == {1'b0, (({1'b0, A} + {1'b0, B})[2:0])})
    );

    // When there is no carry, the RTL forces S[3] low.
    check_no_carry_forces_s_msb_low: assert property (
        @(posedge clk)
        !(({1'b0, A} + {1'b0, B})[4]) |-> (S[3] == 1'b0)
    );

endmodule