module generate_Z_sva (
    input logic CLK,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic [1:0] Z
);
    // Local recomputation of Y (matches RTL equation)
    logic y;
    assign y = (A1 & B2 & C1) | (A2 & B1 & C1) | (A1 & B1 & ~C1) | (A2 & B2 & ~C1);

    ///// Functional mapping /////
    // Z must equal {1'b0, y}.
    check_z_function_mapping: assert property (
        @(posedge CLK) disable iff ($initstate) Z == {1'b0, y}
    );

    ///// Event-driven behavior /////
    // When y rises, Z must be 2'b01 in the same cycle.
    check_update_on_y_rise: assert property (
        @(posedge CLK) disable iff ($initstate) $rose(y) |-> (Z == 2'b01)
    );
    // When y falls, Z must be 2'b00 in the same cycle.
    check_update_on_y_fall: assert property (
        @(posedge CLK) disable iff ($initstate) $fell(y) |-> (Z == 2'b00)
    );
    // Z can only change when y changes.
    check_z_changes_only_if_y_changes: assert property (
        @(posedge CLK) disable iff ($initstate) $changed(Z) |-> $changed(y)
    );
    // If all inputs are stable, Z must be stable.
    check_stable_inputs_imply_stable_Z: assert property (
        @(posedge CLK) disable iff ($initstate) $stable({A1,A2,B1,B2,C1}) |-> $stable(Z)
    );

    ///// Partitioned by C1 /////
    // When C1 is 1, Z[0] equals (A1&B2)|(A2&B1) and MSB is 0.
    check_path_when_C1_is_1: assert property (
        @(posedge CLK) disable iff ($initstate) C1 |-> (Z == {1'b0, ((A1 & B2) | (A2 & B1))})
    );
    // When C1 is 0, Z[0] equals (A1&B1)|(A2&B2) and MSB is 0.
    check_path_when_C1_is_0: assert property (
        @(posedge CLK) disable iff ($initstate) !C1 |-> (Z == {1'b0, ((A1 & B1) | (A2 & B2))})
    );

    ///// Useful corollaries from the logic /////
    // If both A inputs are 0, Z must be 2'b00.
    check_zero_when_A_pair_zero: assert property (
        @(posedge CLK) disable iff ($initstate) (A1 == 1'b0 && A2 == 1'b0) |-> (Z == 2'b00)
    );
    // If both B inputs are 0, Z must be 2'b00.
    check_zero_when_B_pair_zero: assert property (
        @(posedge CLK) disable iff ($initstate) (B1 == 1'b0 && B2 == 1'b0) |-> (Z == 2'b00)
    );
    // If all A and B inputs are 1, Z must be 2'b01 (independent of C1).
    check_one_when_all_ones: assert property (
        @(posedge CLK) disable iff ($initstate) (A1 && A2 && B1 && B2) |-> (Z == 2'b01)
    );
endmodule