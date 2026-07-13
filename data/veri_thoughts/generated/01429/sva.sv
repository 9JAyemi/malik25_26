module and_gate_power_good_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X equals A & B when sampled on A rising edge.
    check_and_equiv_on_A: assert property (
        @(posedge A) X === (A & B)
    );

    // X equals A & B when sampled on B rising edge.
    check_and_equiv_on_B: assert property (
        @(posedge B) X === (A & B)
    );

    // X equals A & B when sampled on X rising edge.
    check_and_equiv_on_X: assert property (
        @(posedge X) X === (A & B)
    );

    // X can only rise when both inputs are HIGH.
    check_x_rise_requires_inputs_high: assert property (
        @(posedge X) (A === 1'b1) && (B === 1'b1)
    );

    // When A rises and B is HIGH, X must be HIGH.
    check_on_A_if_B_high_then_X_high: assert property (
        @(posedge A) (B === 1'b1) |-> (X === 1'b1)
    );

    // When B rises and A is HIGH, X must be HIGH.
    check_on_B_if_A_high_then_X_high: assert property (
        @(posedge B) (A === 1'b1) |-> (X === 1'b1)
    );

    // When A rises and B is LOW, X must be LOW.
    check_on_A_if_B_low_then_X_low: assert property (
        @(posedge A) (B === 1'b0) |-> (X === 1'b0)
    );

    // When B rises and A is LOW, X must be LOW.
    check_on_B_if_A_low_then_X_low: assert property (
        @(posedge B) (A === 1'b0) |-> (X === 1'b0)
    );

endmodule