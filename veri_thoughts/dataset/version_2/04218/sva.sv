module my_xor3_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic X
);

    // X must match the implemented pairwise-AND/or inversion.
    check_function_equation: assert property (
        @(posedge clk) (X == ~((A & B) | (B & C) | (C & A)))
    );

    // 000 must drive X high.
    check_all_zero_drives_one: assert property (
        @(posedge clk) ({A, B, C} == 3'b000) |-> (X == 1'b1)
    );

    // 001 must drive X high.
    check_only_c_high_drives_one: assert property (
        @(posedge clk) ({A, B, C} == 3'b001) |-> (X == 1'b1)
    );

    // 010 must drive X high.
    check_only_b_high_drives_one: assert property (
        @(posedge clk) ({A, B, C} == 3'b010) |-> (X == 1'b1)
    );

    // 011 must drive X low.
    check_b_and_c_high_drive_zero: assert property (
        @(posedge clk) ({A, B, C} == 3'b011) |-> (X == 1'b0)
    );

    // 100 must drive X high.
    check_only_a_high_drives_one: assert property (
        @(posedge clk) ({A, B, C} == 3'b100) |-> (X == 1'b1)
    );

    // 101 must drive X low.
    check_c_and_a_high_drive_zero: assert property (
        @(posedge clk) ({A, B, C} == 3'b101) |-> (X == 1'b0)
    );

    // 110 must drive X low.
    check_a_and_b_high_drive_zero: assert property (
        @(posedge clk) ({A, B, C} == 3'b110) |-> (X == 1'b0)
    );

    // 111 must drive X low.
    check_all_high_drive_zero: assert property (
        @(posedge clk) ({A, B, C} == 3'b111) |-> (X == 1'b0)
    );

endmodule