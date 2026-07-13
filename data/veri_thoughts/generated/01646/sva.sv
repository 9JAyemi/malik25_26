module AND3_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic Z
);
    // Z must equal A & B & C every cycle.
    check_z_is_and_equivalence: assert property (
        @(posedge clk) disable iff (1'b0) Z == (A & B & C)
    );

    // When all inputs are HIGH, Z must be HIGH.
    check_all_high_implies_z_high: assert property (
        @(posedge clk) disable iff (1'b0) (A & B & C) |-> Z
    );

    // If Z is HIGH, all inputs must be HIGH.
    check_z_high_implies_all_high: assert property (
        @(posedge clk) disable iff (1'b0) Z |-> (A & B & C)
    );

    // A rising with B and C HIGH causes Z to rise.
    check_rose_a_causes_rose_z: assert property (
        @(posedge clk) disable iff (1'b0) ($rose(A) && B && C) |-> $rose(Z)
    );

    // B rising with A and C HIGH causes Z to rise.
    check_rose_b_causes_rose_z: assert property (
        @(posedge clk) disable iff (1'b0) ($rose(B) && A && C) |-> $rose(Z)
    );

    // C rising with A and B HIGH causes Z to rise.
    check_rose_c_causes_rose_z: assert property (
        @(posedge clk) disable iff (1'b0) ($rose(C) && A && B) |-> $rose(Z)
    );

    // A rise, B rise, or C rise must occur when Z rises.
    check_rose_z_implies_some_input_rose: assert property (
        @(posedge clk) disable iff (1'b0) $rose(Z) |-> ($rose(A) || $rose(B) || $rose(C))
    );

    // A fall, B fall, or C fall must occur when Z falls.
    check_fell_z_implies_some_input_fell: assert property (
        @(posedge clk) disable iff (1'b0) $fell(Z) |-> ($fell(A) || $fell(B) || $fell(C))
    );

    // If inputs are stable across a cycle, Z must be stable.
    check_stable_inputs_imply_stable_z: assert property (
        @(posedge clk) disable iff (1'b0) $stable({A,B,C}) |=> $stable(Z)
    );
endmodule