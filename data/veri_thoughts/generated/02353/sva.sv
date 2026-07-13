module xor_gate_sva (
    input logic CLK,
    input logic RESETn,
    input logic A,
    input logic B,
    input logic Y
);
    // Y matches sum-of-products definition.
    check_y_sum_of_products: assert property (
        @(posedge CLK) disable iff (!RESETn) Y === ((A & ~B) | (~A & B))
    );

    // Y equals bitwise XOR of A and B.
    check_y_xor_equiv: assert property (
        @(posedge CLK) disable iff (!RESETn) Y === (A ^ B)
    );

    // When inputs are equal, Y is 0.
    check_y_low_when_inputs_equal: assert property (
        @(posedge CLK) disable iff (!RESETn) (A === B) |-> (Y === 1'b0)
    );

    // When inputs differ, Y is 1.
    check_y_high_when_inputs_differ: assert property (
        @(posedge CLK) disable iff (!RESETn) (A !== B) |-> (Y === 1'b1)
    );

    // If Y is 1, exactly one input is 1.
    check_one_hot_inputs_when_y_high: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y === 1'b1) |-> ((A === 1'b1) ^ (B === 1'b1))
    );

    // If Y is 0, inputs are equal.
    check_inputs_equal_when_y_low: assert property (
        @(posedge CLK) disable iff (!RESETn) (Y === 1'b0) |-> (A === B)
    );

    // Truth table: A=0, B=0 -> Y=0.
    check_tt_00: assert property (
        @(posedge CLK) disable iff (!RESETn) (A === 1'b0 && B === 1'b0) |-> (Y === 1'b0)
    );

    // Truth table: A=0, B=1 -> Y=1.
    check_tt_01: assert property (
        @(posedge CLK) disable iff (!RESETn) (A === 1'b0 && B === 1'b1) |-> (Y === 1'b1)
    );

    // Truth table: A=1, B=0 -> Y=1.
    check_tt_10: assert property (
        @(posedge CLK) disable iff (!RESETn) (A === 1'b1 && B === 1'b0) |-> (Y === 1'b1)
    );

    // Truth table: A=1, B=1 -> Y=0.
    check_tt_11: assert property (
        @(posedge CLK) disable iff (!RESETn) (A === 1'b1 && B === 1'b1) |-> (Y === 1'b0)
    );
endmodule