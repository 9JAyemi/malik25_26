module nor_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Z
);
    // Z implements NOR of A and B.
    check_nor_function: assert property (
        @(posedge clk) Z === ~(A | B)
    );

    // Z equals (~A & ~B) (De Morgan consistency).
    check_demorgan_equivalence: assert property (
        @(posedge clk) Z === ((~A) & (~B))
    );

    // Z can be HIGH only when both inputs are LOW.
    check_Z_high_only_if_inputs_low: assert property (
        @(posedge clk) (Z === 1'b1) |-> ((A === 1'b0) && (B === 1'b0))
    );

    // When both inputs are LOW, Z must be HIGH.
    check_inputs_low_imply_Z_high: assert property (
        @(posedge clk) ((A === 1'b0) && (B === 1'b0)) |-> (Z === 1'b1)
    );

    // If A is HIGH, Z must be LOW.
    check_A_high_implies_Z_low: assert property (
        @(posedge clk) (A === 1'b1) |-> (Z === 1'b0)
    );

    // If B is HIGH, Z must be LOW.
    check_B_high_implies_Z_low: assert property (
        @(posedge clk) (B === 1'b1) |-> (Z === 1'b0)
    );

    // If both inputs are HIGH, Z must be LOW.
    check_both_inputs_high_implies_Z_low: assert property (
        @(posedge clk) ((A === 1'b1) && (B === 1'b1)) |-> (Z === 1'b0)
    );

    // If Z is LOW, at least one input must be HIGH.
    check_Z_low_implies_any_input_high: assert property (
        @(posedge clk) (Z === 1'b0) |-> ((A === 1'b1) || (B === 1'b1))
    );

    // If inputs are stable across cycles, Z must be stable.
    check_output_stable_if_inputs_stable: assert property (
        @(posedge clk) $stable({A,B}) |-> $stable(Z)
    );

    // If Z changes, at least one input must have changed.
    check_output_change_implies_input_change: assert property (
        @(posedge clk) $changed(Z) |-> $changed({A,B})
    );
endmodule