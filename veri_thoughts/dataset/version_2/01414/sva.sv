module four_to_one_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);
    // Y must equal the OR of all inputs.
    check_y_is_or: assert property (
        @(posedge CLK) Y == (A | B | C | D)
    );

    // If all inputs are 0, Y must be 0.
    check_y_zero_when_all_zero: assert property (
        @(posedge CLK) (!A && !B && !C && !D) |-> (Y == 1'b0)
    );

    // If any input is 1, Y must be 1.
    check_y_one_when_any_one: assert property (
        @(posedge CLK) (A | B | C | D) |-> (Y == 1'b1)
    );

    // A HIGH implies Y is HIGH.
    check_a_implies_y_one: assert property (
        @(posedge CLK) A |-> (Y == 1'b1)
    );

    // B HIGH implies Y is HIGH.
    check_b_implies_y_one: assert property (
        @(posedge CLK) B |-> (Y == 1'b1)
    );

    // C HIGH implies Y is HIGH.
    check_c_implies_y_one: assert property (
        @(posedge CLK) C |-> (Y == 1'b1)
    );

    // D HIGH implies Y is HIGH.
    check_d_implies_y_one: assert property (
        @(posedge CLK) D |-> (Y == 1'b1)
    );

    // Y rising implies OR is true this cycle.
    check_y_rise_means_or_true: assert property (
        @(posedge CLK) $rose(Y) |-> (A | B | C | D)
    );

    // Y falling implies OR is false this cycle.
    check_y_fall_means_or_false: assert property (
        @(posedge CLK) $fell(Y) |-> !(A | B | C | D)
    );

    // Any change on Y must be due to some input change.
    check_y_change_requires_input_change: assert property (
        @(posedge CLK) ($rose(Y) || $fell(Y)) |-> ($rose(A) || $fell(A) || $rose(B) || $fell(B) || $rose(C) || $fell(C) || $rose(D) || $fell(D))
    );
endmodule