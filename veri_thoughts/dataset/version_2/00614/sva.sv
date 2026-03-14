module three_to_one_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic Y,
    input logic clk
);
    // When A1 and A2 are both 1 at a clock edge, Y must be 1 on the next edge.
    check_y_next_both_one: assert property (
        @(posedge clk) (A1 && A2) |=> (Y == 1'b1)
    );

    // When A1 and A2 are both 0 at a clock edge, Y must be 0 on the next edge.
    check_y_next_both_zero: assert property (
        @(posedge clk) (!A1 && !A2) |=> (Y == 1'b0)
    );

    // When A1=1 and A2=0 at a clock edge, Y must be ~B1 from that edge on the next edge.
    check_y_next_a1_1_a2_0: assert property (
        @(posedge clk) (A1 && !A2) |=> (Y == ~($past(B1)))
    );

    // When A1=0 and A2=1 at a clock edge, Y must be B1 from that edge on the next edge.
    check_y_next_a1_0_a2_1: assert property (
        @(posedge clk) (!A1 && A2) |=> (Y == $past(B1))
    );

    // On every cycle, next Y equals the RTL's full priority case using prior-cycle inputs.
    check_y_next_functional: assert property (
        @(posedge clk) 1'b1 |=> (Y == (
            ($past(A1) && $past(A2)) ? 1'b1 :
            ((!$past(A1) && !$past(A2)) ? 1'b0 :
            (($past(A1) && !$past(A2)) ? ~($past(B1)) : $past(B1)))
        ))
    );

    // When A1 != A2 at a clock edge, next Y equals B1 XOR A1 from that edge.
    check_y_next_when_mismatch_xor: assert property (
        @(posedge clk) (A1 ^ A2) |=> (Y == ($past(B1) ^ $past(A1)))
    );

    // When A1 == A2 at a clock edge, next Y equals A1 from that edge (independent of B1).
    check_y_next_when_equal_matches_a1: assert property (
        @(posedge clk) (A1 == A2) |=> (Y == $past(A1))
    );
endmodule