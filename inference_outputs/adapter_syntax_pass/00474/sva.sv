module XOR_M_sva (
    input logic clk,
    input logic Sgn_X,
    input logic Sgn_Y,
    input logic Sgn_Info
);

    // Sgn_Info must always equal the XOR of Sgn_X and Sgn_Y.
    check_xor_function: assert property (
        @(posedge clk) Sgn_Info == (Sgn_X ^ Sgn_Y)
    );

    // When Sgn_X and Sgn_Y are equal, Sgn_Info must be low.
    check_equal_inputs_drive_low: assert property (
        @(posedge clk) (Sgn_X == Sgn_Y) |-> (Sgn_Info == 1'b0)
    );

    // When Sgn_X and Sgn_Y differ, Sgn_Info must be high.
    check_different_inputs_drive_high: assert property (
        @(posedge clk) (Sgn_X != Sgn_Y) |-> (Sgn_Info == 1'b1)
    );

endmodule