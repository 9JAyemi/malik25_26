module nand3b_inverted_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic invert,
    input logic out_inv
);

    // out_inv matches its combinational equation.
    check_out_inv_equation: assert property (
        @(posedge clk) out_inv == ((~A & invert) | (A & ~invert))
    );

    // out_inv passes A through when invert is low.
    check_out_inv_passthrough: assert property (
        @(posedge clk) !invert |-> (out_inv == A)
    );

    // out_inv inverts A when invert is high.
    check_out_inv_inverted: assert property (
        @(posedge clk) invert |-> (out_inv == ~A)
    );

    // Y matches the NAND of ~A, B, and C.
    check_y_equation: assert property (
        @(posedge clk) Y == ~(~A & B & C)
    );

    // Y is high whenever A is high.
    check_y_high_when_a_high: assert property (
        @(posedge clk) A |-> Y
    );

    // Y is high whenever B is low.
    check_y_high_when_b_low: assert property (
        @(posedge clk) !B |-> Y
    );

    // Y is high whenever C is low.
    check_y_high_when_c_low: assert property (
        @(posedge clk) !C |-> Y
    );

    // Y goes low when ~A, B, and C are all high.
    check_y_low_when_nand_inputs_high: assert property (
        @(posedge clk) (!A && B && C) |-> !Y
    );

    // Y low implies the NAND input term is true.
    check_y_low_only_when_nand_inputs_high: assert property (
        @(posedge clk) !Y |-> (!A && B && C)
    );

endmodule