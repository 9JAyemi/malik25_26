module sky130_fd_sc_hd__o21ai_4_sva (
    input logic CLK,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);
    // Y implements A1 & A2 & ~B1 exactly (including X-propagation).
    check_function_equivalence: assert property (
        @(posedge CLK) Y === (A1 & A2 & ~B1)
    );

    // Y is 0 when B1 is 1.
    check_y_zero_if_b1_one: assert property (
        @(posedge CLK) (B1 === 1'b1) |-> (Y === 1'b0)
    );

    // Y is 0 when A1 is 0.
    check_y_zero_if_a1_zero: assert property (
        @(posedge CLK) (A1 === 1'b0) |-> (Y === 1'b0)
    );

    // Y is 0 when A2 is 0.
    check_y_zero_if_a2_zero: assert property (
        @(posedge CLK) (A2 === 1'b0) |-> (Y === 1'b0)
    );

    // Y is 1 when A1=1, A2=1, and B1=0.
    check_y_one_when_all_true: assert property (
        @(posedge CLK) ((A1 === 1'b1) && (A2 === 1'b1) && (B1 === 1'b0)) |-> (Y === 1'b1)
    );

    // If Y is 1, then A1=1, A2=1, and B1=0.
    check_inputs_required_when_y_one: assert property (
        @(posedge CLK) (Y === 1'b1) |-> ((A1 === 1'b1) && (A2 === 1'b1) && (B1 === 1'b0))
    );

    // Rising edge of Y implies inputs produce 1.
    check_y_rise_implies_inputs_true: assert property (
        @(posedge CLK) $rose(Y) |-> ((A1 === 1'b1) && (A2 === 1'b1) && (B1 === 1'b0))
    );

    // Falling edge of Y implies not all enabling inputs are true.
    check_y_fall_implies_inputs_not_all: assert property (
        @(posedge CLK) $fell(Y) |-> ((A1 !== 1'b1) || (A2 !== 1'b1) || (B1 !== 1'b0))
    );

    // With B1=0, Y equals A1 & A2.
    check_y_equals_a1a2_when_b1_zero: assert property (
        @(posedge CLK) (B1 === 1'b0) |-> (Y === (A1 & A2))
    );

    // With A1=1 and B1=0, Y equals A2.
    check_y_equals_a2_when_a1_and_not_b1: assert property (
        @(posedge CLK) ((A1 === 1'b1) && (B1 === 1'b0)) |-> (Y === A2)
    );

    // With A2=1 and B1=0, Y equals A1.
    check_y_equals_a1_when_a2_and_not_b1: assert property (
        @(posedge CLK) ((A2 === 1'b1) && (B1 === 1'b0)) |-> (Y === A1)
    );

    // With A1=1 and A2=1, Y equals ~B1.
    check_y_equals_not_b1_when_both_a_high: assert property (
        @(posedge CLK) ((A1 === 1'b1) && (A2 === 1'b1)) |-> (Y === ~B1)
    );
endmodule