module alu2_sva (
    input logic        clk,
    input logic [31:0] srca,
    input logic [31:0] srcb,
    input logic [1:0]  alucontrol,
    input logic [31:0] aluresult,
    input logic [3:0]  aluflags
);

// aluresult matches the RTL add/sub/and/or path.
    check_aluresult_function: assert property (
        @(posedge clk)
        aluresult == (alucontrol[0] ? (srca + ~srcb + 1) : (srca + srcb))
    );

// aluflags[3:2] encode zero and sign from aluresult.
    check_aluflags_zero_sign: assert property (
        @(posedge clk)
        aluflags[3:2] == {aluresult[31], (aluresult == 32'h0)}
    );

// aluflags[1] is cout & ~alucontrol[1].
    check_aluflags_cout_bit: assert property (
        @(posedge clk)
        aluflags[1] == ((alucontrol[0] ? (srca + ~srcb + 1) : (srca + srcb)) >= 32'h100000000)
    );

// aluflags[0] matches the RTL zero-extend/carry/MSB parity equation.
    check_aluflags_zero_extend_parity: assert property (
        @(posedge clk)
        aluflags[0] == (
            (alucontrol[0] ? (srca + ~srcb + 1) : (srca + srcb)) >= 32'h100000000 &&
            (srca[31] == srcb[31]) &&
            ((srca[31] ^ aluresult[31]) == 1'b1)
        )
    );

// Zero plus zero produces zero with zero flags.
    check_zero_plus_zero: assert property (
        @(posedge clk)
        (srca == 32'h0 && srcb == 32'h0) |-> (aluresult == 32'h0 && aluflags == 4'b0000)
    );

// Zero on srcb passes srca through with zero flags.
    check_zero_srcb_passthrough: assert property (
        @(posedge clk)
        (srcb == 32'h0) |-> (aluresult == srca && aluflags == 4'b0000)
    );

// Zero on srca passes srcb through with zero flags.
    check_zero_srca_passthrough: assert property (
        @(posedge clk)
        (srca == 32'h0) |-> (aluresult == srcb && aluflags == 4'b0000)
    );

// Subtracting equal operands yields zero with zero flags.
    check_sub_equal_operands_zero: assert property (
        @(posedge clk)
        (alucontrol[0] && (srca == srcb)) |-> (aluresult == 32'h0 && aluflags == 4'b0000)
    );

// Subtracting one from zero yields all ones with zero flags.
    check_sub_one_from_zero_all_ones: assert property (
        @(posedge clk)
        (alucontrol[0] && (srca == 32'h0 && srcb == 32'h1)) |-> (aluresult == 32'hFFFFFFFF && aluflags == 4'b0000)
    );

// Subtracting zero from one yields one with zero flags.
    check_sub_zero_from_one_one: assert property (
        @(posedge clk)
        (alucontrol[0] && (srca == 32'h1 && srcb == 32'h0)) |-> (aluresult == 32'h00000001 && aluflags == 4'b0000)
    );

// Subtracting one from all ones yields zero with zero flags.
    check_sub_one_from_all_ones_zero: assert property (
        @(posedge clk)
        (alucontrol[0] && (srca == 32'hFFFFFFFF && srcb == 32'h00000001)) |-> (aluresult == 32'h00000000 && aluflags == 4'b0000)
    );

endmodule
