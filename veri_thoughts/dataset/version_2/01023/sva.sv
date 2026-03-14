module sky130_fd_sc_lp__cap_1_sva (
    input logic A,
    input logic P,
    input logic n,
    input logic C
);
    // P equals A & ~n at each sample
    check_p_equals_a_and_notn: assert property (
        @(posedge C) P == (A & ~n)
    );

    // When n is 1, P must be 0
    check_p_zero_when_n_high: assert property (
        @(posedge C) n |-> (P == 1'b0)
    );

    // When n is 0, P equals A
    check_p_equals_a_when_n_low: assert property (
        @(posedge C) !n |-> (P == A)
    );

    // When A is 0, P must be 0
    check_p_zero_when_a_low: assert property (
        @(posedge C) (A == 1'b0) |-> (P == 1'b0)
    );

    // When A is 1 and n is 0, P must be 1
    check_p_one_when_a1_n0: assert property (
        @(posedge C) (A && !n) |-> (P == 1'b1)
    );

    // P high implies A is 1 and n is 0
    check_p_high_implies_inputs: assert property (
        @(posedge C) (P == 1'b1) |-> (A && !n)
    );

    // P low implies A is 0 or n is 1
    check_p_low_implies_inputs: assert property (
        @(posedge C) (P == 1'b0) |-> (!A || n)
    );
endmodule