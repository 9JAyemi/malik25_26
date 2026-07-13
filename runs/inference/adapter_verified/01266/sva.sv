module AND4_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Z
);

// Z equals the AND of all four inputs.
    check_function_equivalence: assert property (
        @(posedge clk) Z == (A & B & C & D)
    );

// All inputs high drives Z high.
    check_all_high_drives_high: assert property (
        @(posedge clk) (A & B & C & D) |-> Z
    );

// A low forces Z low.
    check_a_low_forces_low: assert property (
        @(posedge clk) !A |-> !Z
    );

// B low forces Z low.
    check_b_low_forces_low: assert property (
        @(posedge clk) !B |-> !Z
    );

// C low forces Z low.
    check_c_low_forces_low: assert property (
        @(posedge clk) !C |-> !Z
    );

// D low forces Z low.
    check_d_low_forces_low: assert property (
        @(posedge clk) !D |-> !Z
    );

// Z high implies all inputs are high.
    check_high_output_requires_all_high: assert property (
        @(posedge clk) Z |-> (A & B & C & D)
    );

endmodule
