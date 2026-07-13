module nor4_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // Y matches the implemented combinational equation.
    check_output_equation: assert property (
        @(posedge clk) Y == ((~(A | B | C)) | D)
    );

    // When D is low, Y reduces to the NOR of A, B, and C.
    check_d_low_reduces_to_nor3: assert property (
        @(posedge clk) !D |-> (Y == ~(A | B | C))
    );

    // A high D input forces Y high.
    check_d_high_forces_y_high: assert property (
        @(posedge clk) D |-> Y
    );

    // With D low, any high input among A, B, or C forces Y low.
    check_abc_high_with_d_low_forces_y_low: assert property (
        @(posedge clk) (!D && (A || B || C)) |-> !Y
    );

    // If all inputs are stable across samples, Y stays stable too.
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge clk) $stable({A, B, C, D}) |-> $stable(Y)
    );

endmodule