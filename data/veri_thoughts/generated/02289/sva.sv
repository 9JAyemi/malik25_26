module and4_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1,
    input logic Y,
    input logic VPWR,
    input logic VGND
);

    // Y must equal the logical AND of A1, A2, B1, C1.
    check_and_function: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or
          negedge A1 or negedge A2 or negedge B1 or negedge C1)
        Y == (A1 & A2 & B1 & C1)
    );

    // If Y is HIGH, all inputs must be HIGH.
    y_high_implies_all_inputs_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or
          negedge A1 or negedge A2 or negedge B1 or negedge C1)
        (Y == 1'b1) |-> (A1 && A2 && B1 && C1)
    );

    // If any input is LOW, Y must be LOW (A1 low case).
    a1_low_forces_y_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or
          negedge A1 or negedge A2 or negedge B1 or negedge C1)
        (!A1) |-> (!Y)
    );

    // If any input is LOW, Y must be LOW (A2 low case).
    a2_low_forces_y_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or
          negedge A1 or negedge A2 or negedge B1 or negedge C1)
        (!A2) |-> (!Y)
    );

    // If any input is LOW, Y must be LOW (B1 low case).
    b1_low_forces_y_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or
          negedge A1 or negedge A2 or negedge B1 or negedge C1)
        (!B1) |-> (!Y)
    );

    // If any input is LOW, Y must be LOW (C1 low case).
    c1_low_forces_y_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or
          negedge A1 or negedge A2 or negedge B1 or negedge C1)
        (!C1) |-> (!Y)
    );

    // If all inputs are HIGH, Y must be HIGH.
    all_inputs_high_implies_y_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or
          negedge A1 or negedge A2 or negedge B1 or negedge C1)
        (A1 && A2 && B1 && C1) |-> (Y == 1'b1)
    );

    // A rising Y requires all inputs to be HIGH at that sample.
    y_rise_requires_all_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or
          negedge A1 or negedge A2 or negedge B1 or negedge C1)
        $rose(Y) |-> (A1 && A2 && B1 && C1)
    );

    // A falling Y requires not all inputs HIGH at that sample.
    y_fall_requires_not_all_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or
          negedge A1 or negedge A2 or negedge B1 or negedge C1)
        $fell(Y) |-> !(A1 && A2 && B1 && C1)
    );

    // If Y is LOW, at least one input must be LOW.
    y_low_implies_some_input_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge C1 or
          negedge A1 or negedge A2 or negedge B1 or negedge C1)
        (Y == 1'b0) |-> !(A1 && A2 && B1 && C1)
    );

endmodule