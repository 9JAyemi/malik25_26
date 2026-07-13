module XOR_M_sva (
    input logic clk,
    input logic Sgn_X,
    input logic Sgn_Y,
    input logic Sgn_Info
);

// Sgn_Info must equal the XOR of Sgn_X and Sgn_Y.
    check_xor_function: assert property (
        @(posedge clk) Sgn_Info == (Sgn_X ^ Sgn_Y)
    );

// When Sgn_X equals Sgn_Y, Sgn_Info must be 0.
    check_equal_inputs_zero: assert property (
        @(posedge clk) (Sgn_X == Sgn_Y) |-> (Sgn_Info == 1'b0)
    );

// When Sgn_X differs from Sgn_Y, Sgn_Info must be 1.
    check_different_inputs_one: assert property (
        @(posedge clk) (Sgn_X != Sgn_Y) |-> (Sgn_Info == 1'b1)
    );

endmodule
