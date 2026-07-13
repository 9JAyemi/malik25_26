module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] SUM,
    input logic COUT
);

    // Sampling clock; DUT is combinational and has no reset.

    // SUM[0] is the XOR of A[0], B[0], and CIN.
    check_sum_bit0_xor: assert property (
        @(posedge clk) SUM[0] == (A[0] ^ B[0] ^ CIN)
    );

    // SUM[1] matches bit 1 of the 5-bit addition result.
    check_sum_bit1_matches_addition: assert property (
        @(posedge clk) SUM[1] == (({1'b0, A} + {1'b0, B} + {4'b0000, CIN})[1])
    );

    // SUM[2] matches bit 2 of the 5-bit addition result.
    check_sum_bit2_matches_addition: assert property (
        @(posedge clk) SUM[2] == (({1'b0, A} + {1'b0, B} + {4'b0000, CIN})[2])
    );

    // SUM[3] matches bit 3 of the 5-bit addition result.
    check_sum_bit3_matches_addition: assert property (
        @(posedge clk) SUM[3] == (({1'b0, A} + {1'b0, B} + {4'b0000, CIN})[3])
    );

    // COUT matches the carry bit of the 5-bit addition result.
    check_cout_matches_addition: assert property (
        @(posedge clk) COUT == (({1'b0, A} + {1'b0, B} + {4'b0000, CIN})[4])
    );

    // SUM matches the lower four bits of A + B + CIN.
    check_sum_vector_matches_addition: assert property (
        @(posedge clk) SUM == (({1'b0, A} + {1'b0, B} + {4'b0000, CIN})[3:0])
    );

    // COUT and SUM together equal the full 5-bit addition result.
    check_total_result_matches_addition: assert property (
        @(posedge clk) {COUT, SUM} == ({1'b0, A} + {1'b0, B} + {4'b0000, CIN})
    );

endmodule