module alu2_sva (
    input logic        clk,
    input logic [31:0] srca,
    input logic [31:0] srcb,
    input logic [1:0]  alucontrol,
    input logic [31:0] aluresult,
    input logic [3:0]  aluflags
);

    // No RTL clock or reset; sample combinational behavior on clk.

    // ADD mode returns the 32-bit sum of srca and srcb.
    check_add_result: assert property (
        @(posedge clk) (alucontrol == 2'b00) |-> (aluresult == (srca + srcb))
    );

    // SUB mode returns the 32-bit sum of srca and the two's-complement of srcb.
    check_sub_result: assert property (
        @(posedge clk) (alucontrol == 2'b01) |-> (aluresult == (srca + (~srcb) + 32'd1))
    );

    // AND mode returns the bitwise AND of srca and srcb.
    check_and_result: assert property (
        @(posedge clk) (alucontrol == 2'b10) |-> (aluresult == (srca & srcb))
    );

    // OR mode returns the bitwise OR of srca and srcb.
    check_or_result: assert property (
        @(posedge clk) (alucontrol == 2'b11) |-> (aluresult == (srca | srcb))
    );

    // ADD mode sets carry-out from the 33-bit addition.
    check_add_carry: assert property (
        @(posedge clk) (alucontrol == 2'b00) |-> (({1'b0, aluresult} == ({1'b0, srca} + {1'b0, srcb})) |-> (aluflags[1] == 1'b1))
    );

    // SUB mode sets carry-out from the 33-bit addition of srca + (~srcb) + 1.
    check_sub_carry: assert property (
        @(posedge clk) (alucontrol == 2'b01) |-> (({1'b0, aluresult} == ({1'b0, srca} + {1'b0, (~srcb)} + 33'd1))) |-> (aluflags[1] == 1'b1)
    );

    // AND mode clears carry-out.
    check_and_carry: assert property (
        @(posedge clk) (alucontrol == 2'b10) |-> (aluflags[1] == 1'b0)
    );

    // OR mode clears carry-out.
    check_or_carry: assert property (
        @(posedge clk) (alucontrol == 2'b11) |-> (aluflags[1] == 1'b0)
    );

    // ADD mode sets zero flag when the sum is zero.
    check_add_zero_flag: assert property (
        @(posedge clk) (alucontrol == 2'b00) |-> ((aluresult == 32'd0) |-> (aluflags[0] == 1'b1))
    );

    // SUB mode sets zero flag when the difference is zero.
    check_sub_zero_flag: assert property (
        @(posedge clk) (alucontrol == 2'b01) |-> ((aluresult == 32'd0) |-> (aluflags[0] == 1'b1))
    );

    // AND mode sets zero flag when the AND result is zero.
    check_and_zero_flag: assert property (
        @(posedge clk) (alucontrol == 2'b10) |-> ((aluresult == 32'd0) |-> (aluflags[0] == 1'b1))
    );

    // OR mode sets zero flag when the OR result is zero.
    check_or_zero_flag: assert property (
        @(posedge clk) (alucontrol == 2'b11) |-> ((aluresult == 32'd0) |-> (aluflags[0] == 1'b1))
    );

    // ADD mode sets sign flag from the 32-bit sum sign.
    check_add_sign_flag: assert property (
        @(posedge clk) (alucontrol == 2'b00) |-> (({1'b0, aluresult} == ({1'b0, srca} + {1'b0, srcb})) |-> (aluflags[3] == aluresult[31]))
    );

    // SUB mode sets sign flag from the 32-bit difference sign.
    check_sub_sign_flag: assert property (
        @(posedge clk) (alucontrol == 2'b01) |-> (({1'b0, aluresult} == ({1'b0, srca} + {1'b0, (~srcb)} + 33'd1))) |-> (aluflags[3] == aluresult[31])
    );

    // AND mode sets sign flag from srca sign.
    check_and_sign_flag: assert property (
        @(posedge clk) (alucontrol == 2'b10) |-> (aluflags[3] == srca[31])
    );

    // OR mode sets sign flag from srca sign.
    check_or_sign_flag: assert property (
        @(posedge clk) (alucontrol == 2'b11) |-> (aluflags[3] == srca[31])
    );

endmodule