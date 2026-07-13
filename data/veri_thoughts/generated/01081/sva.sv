module custom_module_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    ///// Functional equivalence /////
    // Y equals the boolean function A1 && !A2 && A3 && B1 && !B2 (4-state exact).
    check_y_function_equivalence: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge Y)
            (Y === (A1 && !A2 && A3 && B1 && !B2))
    );

    ///// Truth table implications /////
    // When the exact enable condition holds, Y must be 1.
    check_y_when_condition_true: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge Y)
            (A1 && !A2 && A3 && B1 && !B2) |-> (Y === 1'b1)
    );

    // A1 LOW forces Y LOW.
    check_y_zero_when_A1_low: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge Y)
            (!A1) |-> (Y === 1'b0)
    );

    // A2 HIGH forces Y LOW.
    check_y_zero_when_A2_high: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge Y)
            (A2) |-> (Y === 1'b0)
    );

    // A3 LOW forces Y LOW.
    check_y_zero_when_A3_low: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge Y)
            (!A3) |-> (Y === 1'b0)
    );

    // B1 LOW forces Y LOW.
    check_y_zero_when_B1_low: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge Y)
            (!B1) |-> (Y === 1'b0)
    );

    // B2 HIGH forces Y LOW.
    check_y_zero_when_B2_high: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge Y)
            (B2) |-> (Y === 1'b0)
    );

    ///// Output-to-input implications /////
    // If Y is HIGH, A1 must be HIGH.
    check_inputs_when_y_high_A1: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge Y)
            (Y === 1'b1) |-> (A1 === 1'b1)
    );

    // If Y is HIGH, A2 must be LOW.
    check_inputs_when_y_high_A2: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge Y)
            (Y === 1'b1) |-> (A2 === 1'b0)
    );

    // If Y is HIGH, A3 must be HIGH.
    check_inputs_when_y_high_A3: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge Y)
            (Y === 1'b1) |-> (A3 === 1'b1)
    );

    // If Y is HIGH, B1 must be HIGH.
    check_inputs_when_y_high_B1: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge Y)
            (Y === 1'b1) |-> (B1 === 1'b1)
    );

    // If Y is HIGH, B2 must be LOW.
    check_inputs_when_y_high_B2: assert property (
        @(posedge A1 or posedge A2 or posedge A3 or posedge B1 or posedge B2 or posedge Y)
            (Y === 1'b1) |-> (B2 === 1'b0)
    );

endmodule