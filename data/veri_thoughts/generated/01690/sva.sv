module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] OUT
);
    // DUT is purely combinational with no clock/reset; assertions are sampled on external clk.

    // OUT[0] equals bit 0 of (A + B).
    check_out0_eq_sum0: assert property (
        @(posedge clk) OUT[0] == (A + B)[0]
    );

    // OUT[1] equals XOR of bits 0 and 1 of (A + B).
    check_out1_eq_xor_lsb: assert property (
        @(posedge clk) OUT[1] == ((A + B)[0] ^ (A + B)[1])
    );

    // OUT[2] equals OR of bits 0 and 1 of (A + B).
    check_out2_eq_or_lsb: assert property (
        @(posedge clk) OUT[2] == ((A + B)[0] | (A + B)[1])
    );

    // OUT[3] equals OR of bits 0 and 1 of (A + B).
    check_out3_eq_or_lsb: assert property (
        @(posedge clk) OUT[3] == ((A + B)[0] | (A + B)[1])
    );

    // OUT must be one of 0000, 1111, 1110, or 1101.
    check_output_value_domain: assert property (
        @(posedge clk) OUT inside {4'b0000, 4'b1111, 4'b1110, 4'b1101}
    );

    // If OUT[2] is 0 then all OUT bits are 0.
    check_out2_zero_implies_zero: assert property (
        @(posedge clk) (OUT[2] == 1'b0) |-> (OUT == 4'b0000)
    );

    // If OUT[0] is 1 then OUT[2] and OUT[3] are 1.
    check_out0_one_implies_msbs_one: assert property (
        @(posedge clk) OUT[0] |-> (OUT[2] && OUT[3])
    );

    // If OUT[1] is 1 then OUT[2] and OUT[3] are 1.
    check_out1_one_implies_msbs_one: assert property (
        @(posedge clk) OUT[1] |-> (OUT[2] && OUT[3])
    );

    // If A[1:0] and B[1:0] are stable, OUT remains stable.
    check_stable_on_low2bits_stable: assert property (
        @(posedge clk) $stable({A[1:0], B[1:0]}) |-> $stable(OUT)
    );

    // If all inputs are stable, OUT remains stable (combinational behavior).
    check_stable_on_inputs_stable: assert property (
        @(posedge clk) $stable({A, B}) |-> $stable(OUT)
    );

endmodule