module half_adder_sva (
    input logic A,
    input logic B,
    input logic SUM,
    input logic CARRY_OUT
);
    // Pure combinational DUT with no clock/reset; sample on any A/B edge.

    // SUM equals A XOR B on any input edge.
    check_sum_equals_xor: assert property (
        @(posedge A or negedge A or posedge B or negedge B) SUM == (A ^ B)
    );

    // CARRY_OUT equals A AND B on any input edge.
    check_carry_equals_and: assert property (
        @(posedge A or negedge A or posedge B or negedge B) CARRY_OUT == (A & B)
    );

    // When A=0 and B=0 then SUM=0 and CARRY_OUT=0.
    check_truth_00: assert property (
        @(posedge A or negedge A or posedge B or negedge B) ((A==1'b0)&&(B==1'b0)) |-> ((SUM==1'b0)&&(CARRY_OUT==1'b0))
    );

    // When A=0 and B=1 then SUM=1 and CARRY_OUT=0.
    check_truth_01: assert property (
        @(posedge A or negedge A or posedge B or negedge B) ((A==1'b0)&&(B==1'b1)) |-> ((SUM==1'b1)&&(CARRY_OUT==1'b0))
    );

    // When A=1 and B=0 then SUM=1 and CARRY_OUT=0.
    check_truth_10: assert property (
        @(posedge A or negedge A or posedge B or negedge B) ((A==1'b1)&&(B==1'b0)) |-> ((SUM==1'b1)&&(CARRY_OUT==1'b0))
    );

    // When A=1 and B=1 then SUM=0 and CARRY_OUT=1.
    check_truth_11: assert property (
        @(posedge A or negedge A or posedge B or negedge B) ((A==1'b1)&&(B==1'b1)) |-> ((SUM==1'b0)&&(CARRY_OUT==1'b1))
    );

    // SUM and CARRY_OUT are never both HIGH.
    check_outputs_mutex: assert property (
        @(posedge A or negedge A or posedge B or negedge B) !(SUM & CARRY_OUT)
    );

    // If CARRY_OUT is HIGH then both inputs are HIGH.
    check_carry_high_inputs_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B) CARRY_OUT |-> (A && B)
    );

    // If SUM is HIGH then inputs differ.
    check_sum_high_inputs_differ: assert property (
        @(posedge A or negedge A or posedge B or negedge B) SUM |-> (A ^ B)
    );

    // If SUM is LOW then inputs are equal.
    check_sum_low_inputs_equal: assert property (
        @(posedge A or negedge A or posedge B or negedge B) (SUM==1'b0) |-> (A==B)
    );
endmodule