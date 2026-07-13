module XOR_M_sva (
    input logic clk,
    input logic Sgn_X,
    input logic Sgn_Y,
    input logic Sgn_Info
);

    // Output must always be the XOR of the two inputs.
    check_xor_function: assert property (
        @(posedge clk) Sgn_Info == (Sgn_X ^ Sgn_Y)
    );

    // 0 ^ 0 must produce 0.
    check_xor_00_case: assert property (
        @(posedge clk) (Sgn_X == 1'b0 && Sgn_Y == 1'b0) |-> (Sgn_Info == 1'b0)
    );

    // 0 ^ 1 must produce 1.
    check_xor_01_case: assert property (
        @(posedge clk) (Sgn_X == 1'b0 && Sgn_Y == 1'b1) |-> (Sgn_Info == 1'b1)
    );

    // 1 ^ 0 must produce 1.
    check_xor_10_case: assert property (
        @(posedge clk) (Sgn_X == 1'b1 && Sgn_Y == 1'b0) |-> (Sgn_Info == 1'b1)
    );

    // 1 ^ 1 must produce 0.
    check_xor_11_case: assert property (
        @(posedge clk) (Sgn_X == 1'b1 && Sgn_Y == 1'b1) |-> (Sgn_Info == 1'b0)
    );

endmodule