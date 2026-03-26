module twos_complement_sva (
    input logic clk,        // sampling clock for combinational DUT
    input logic [3:0] A,
    input logic [3:0] OUT
);

    // OUT must equal the 4-bit two's complement of A.
    check_twos_complement_function: assert property (
        @(posedge clk) OUT == (~A + 4'b0001)
    );

    // A and OUT must add to zero modulo 16.
    check_additive_inverse: assert property (
        @(posedge clk) (A + OUT) == 4'b0000
    );

    // Zero input must produce zero output.
    check_zero_maps_to_zero: assert property (
        @(posedge clk) (A == 4'b0000) |-> (OUT == 4'b0000)
    );

    // 4'b1000 must map to itself in 4-bit two's complement.
    check_min_value_self_inverse: assert property (
        @(posedge clk) (A == 4'b1000) |-> (OUT == 4'b1000)
    );

    // Two's complement preserves the least-significant bit.
    check_lsb_preserved: assert property (
        @(posedge clk) OUT[0] == A[0]
    );

endmodule