module nand4_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);
    // Y equals (~(A & B)) & (~(C & D)).
    check_y_eq_nands_and_form: assert property (
        @(posedge CLK) Y == ((~(A & B)) & (~(C & D)))
    );

    // Y equals ~((A & B) | (C & D)) by De Morgan.
    check_y_eq_demorgan_or_form: assert property (
        @(posedge CLK) Y == ~( (A & B) | (C & D) )
    );

    // If A and B are both 1, Y must be 0.
    check_ab_high_forces_y_low: assert property (
        @(posedge CLK) (A & B) |-> (Y == 1'b0)
    );

    // If C and D are both 1, Y must be 0.
    check_cd_high_forces_y_low: assert property (
        @(posedge CLK) (C & D) |-> (Y == 1'b0)
    );

    // If neither A&B nor C&D is 1, Y must be 1.
    check_no_pair_and_implies_y_high: assert property (
        @(posedge CLK) (!(A & B) && !(C & D)) |-> (Y == 1'b1)
    );

    // If Y is 1, then neither A&B nor C&D is 1.
    check_y_high_implies_no_pair_and: assert property (
        @(posedge CLK) Y |-> (!(A & B) && !(C & D))
    );

    // If Y is 0, then at least one of A&B or C&D is 1.
    check_y_low_implies_some_pair_and: assert property (
        @(posedge CLK) (!Y) |-> ((A & B) || (C & D))
    );
endmodule