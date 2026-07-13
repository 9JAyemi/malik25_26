module my_or4_sva (
    input logic CLK,  // sampling clock for assertions
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);
    // X equals bitwise OR of inputs.
    check_x_equals_or: assert property (
        @(posedge CLK) X === (A | B | C | D)
    );

    // All inputs LOW imply X is LOW.
    check_all_zero_implies_x_zero: assert property (
        @(posedge CLK) (A==1'b0 && B==1'b0 && C==1'b0 && D==1'b0) |-> (X==1'b0)
    );

    // A HIGH implies X HIGH.
    check_a_high_implies_x_high: assert property (
        @(posedge CLK) (A==1'b1) |-> (X==1'b1)
    );

    // B HIGH implies X HIGH.
    check_b_high_implies_x_high: assert property (
        @(posedge CLK) (B==1'b1) |-> (X==1'b1)
    );

    // C HIGH implies X HIGH.
    check_c_high_implies_x_high: assert property (
        @(posedge CLK) (C==1'b1) |-> (X==1'b1)
    );

    // D HIGH implies X HIGH.
    check_d_high_implies_x_high: assert property (
        @(posedge CLK) (D==1'b1) |-> (X==1'b1)
    );

    // X LOW implies all inputs LOW.
    check_x_zero_implies_all_zero: assert property (
        @(posedge CLK) (X==1'b0) |-> (A==1'b0 && B==1'b0 && C==1'b0 && D==1'b0)
    );

    // X HIGH implies at least one input HIGH.
    check_x_one_implies_any_one: assert property (
        @(posedge CLK) (X==1'b1) |-> (A | B | C | D)
    );

    // X rising edge implies at least one input rose.
    check_x_rose_caused_by_input_rise: assert property (
        @(posedge CLK) $rose(X) |-> ($rose(A) || $rose(B) || $rose(C) || $rose(D))
    );

    // X falling edge implies at least one input fell.
    check_x_fell_caused_by_input_fall: assert property (
        @(posedge CLK) $fell(X) |-> ($fell(A) || $fell(B) || $fell(C) || $fell(D))
    );
endmodule