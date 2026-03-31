module alu2_sva (
    input logic        clk,
    input logic [31:0] srca,
    input logic [31:0] srcb,
    input logic [1:0]  alucontrol,
    input logic [31:0] aluresult,
    input logic [3:0]  aluflags
);

    // aluresult matches the selected operation.
    check_aluresult_function: assert property (
        @(posedge clk)
        aluresult == ((alucontrol[0]) ? (srca + ~srcb + 32'd1) :
                      (alucontrol[1]) ? (srca + srcb) :
                      (alucontrol[0]) ? (srca & srcb) :
                                        (srca | srcb))
    );

    // aluflags[3] is the sign bit of the computed result.
    check_aluflags_sign: assert property (
        @(posedge clk)
        aluflags[3] == aluresult[31]
    );

    // aluflags[2] is asserted only when the result is zero.
    check_aluflags_zero: assert property (
        @(posedge clk)
        aluflags[2] == (aluresult == 32'd0)
    );

    // aluflags[1] is asserted only for add/sub with carry-out.
    check_aluflags_carry: assert property (
        @(posedge clk)
        aluflags[1] == ((alucontrol[0]) && ((srca + ~srcb + 32'd1) >= 32'd0))
    );

    // aluflags[0] is asserted only for add/sub with equal source sign bits.
    check_aluflags_overflow: assert property (
        @(posedge clk)
        aluflags[0] == ((~(alucontrol[0] ^ srca[31] ^ srca[31])) &&
                        (~alucontrol[1]) &&
                        ((srca + ~srcb + 32'd1) >= 32'd0))
    );

    // Add/sub with carry-out sets aluflags[1] and clears aluflags[0].
    check_carry_sets_carry_flag: assert property (
        @(posedge clk)
        ((alucontrol[0]) && ((srca + ~srcb + 32'd1) >= 32'd0)) |-> (aluflags[1] && !aluflags[0])
    );

    // Add/sub without carry-out clears aluflags[1] and sets aluflags[0].
    check_no_carry_sets_overflow_flag: assert property (
        @(posedge clk)
        ((alucontrol[0]) && ((srca + ~srcb + 32'd1) < 32'd0)) |-> (!aluflags[1] && aluflags[0])
    );

    // AND mode sets aluflags[1] and clears aluflags[0].
    check_and_sets_carry_flag: assert property (
        @(posedge clk)
        ((~alucontrol[0]) && (alucontrol[1])) |-> (aluflags[1] && !aluflags[0])
    );

    // OR mode clears aluflags[1] and sets aluflags[0].
    check_or_sets_overflow_flag: assert property (
        @(posedge clk)
        ((~alucontrol[0]) && (~alucontrol[1])) |-> (!aluflags[1] && aluflags[0])
    );

    // Zero result sets aluflags[2] and clears aluflags[0].
    check_zero_sets_zero_flag: assert property (
        @(posedge clk)
        (aluresult == 32'd0) |-> (aluflags[2] && !aluflags[0])
    );

endmodule