module my_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    default clocking cb @(posedge A1 or negedge A1 or
                          posedge A2 or negedge A2 or
                          posedge A3 or negedge A3 or
                          posedge B1 or negedge B1 or
                          posedge Y  or negedge Y);
        input #0 Y, A1, A2, A3, B1;
    endclocking

    // Y implements the buffered NAND of B1 and the OR of A1/A2/A3.
    check_y_function: assert property (
        @(cb) Y == ~(B1 & (A1 | A2 | A3))
    );

    // If B1 is low, Y must be high.
    check_b1_low_forces_y_high: assert property (
        @(cb) !B1 |-> Y
    );

    // If all A inputs are low, Y must be high.
    check_all_a_low_forces_y_high: assert property (
        @(cb) !(A1 | A2 | A3) |-> Y
    );

    // If B1 is high and any A input is high, Y must be low.
    check_active_inputs_force_y_low: assert property (
        @(cb) (B1 && (A1 | A2 | A3)) |-> !Y
    );

    // A falling Y can only occur when both NAND inputs are high.
    check_y_fall_has_valid_cause: assert property (
        @(cb) $fell(Y) |-> (B1 && (A1 | A2 | A3))
    );

    // A rising Y can only occur when B1 is low or all A inputs are low.
    check_y_rise_has_valid_cause: assert property (
        @(cb) $rose(Y) |-> (!B1 || !(A1 | A2 | A3))
    );

endmodule