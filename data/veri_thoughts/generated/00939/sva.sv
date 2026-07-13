module adder_4bit_sva (
    input logic aclr,
    input logic clock,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] S,
    input logic COUT
);
    // S is driven to zero while asynchronous reset is asserted low.
    check_reset_clears_S: assert property (
        @(posedge clock) (!aclr) |-> (S == 4'b0000)
    );

    // COUT equals the carry-out (MSB) of A + B + CIN.
    check_cout_matches_arithmetic: assert property (
        @(posedge clock) disable iff (!aclr)
            COUT == ({1'b0, A} + {1'b0, B} + CIN)[4]
    );

    // Sequential update rule: if last cycle was not in reset, S loads sum on COUT=1 else holds.
    check_sequential_update: assert property (
        @(posedge clock) disable iff (!aclr)
            $past(aclr) |-> S == ( $past(COUT)
                                   ? ({1'b0, $past(A)} + {1'b0, $past(B)} + $past(CIN))[3:0]
                                   : $past(S) )
    );

    // When COUT was 1 in the previous cycle, S equals the previous cycle's sum.
    check_load_on_cout: assert property (
        @(posedge clock) disable iff (!aclr)
            $past(aclr) && $past(COUT) |-> S == ({1'b0, $past(A)} + {1'b0, $past(B)} + $past(CIN))[3:0]
    );

    // When COUT was 0 in the previous cycle, S holds its previous value.
    check_hold_when_cout_zero: assert property (
        @(posedge clock) disable iff (!aclr)
            $past(aclr) && !$past(COUT) |-> S == $past(S)
    );

    // Any change in S across cycles implies COUT was 1 in the previous cycle.
    check_change_implies_prev_cout: assert property (
        @(posedge clock) disable iff (!aclr)
            $past(aclr) && (S != $past(S)) |-> $past(COUT)
    );

    // After reset deassertion, S remains zero until a cycle where COUT is 1.
    check_zero_until_first_cout: assert property (
        @(posedge clock) disable iff (!aclr)
            $rose(aclr) |-> (S == 4'b0000 until_with COUT)
    );
endmodule