module MUX2_sva (
    input logic A,
    input logic B,
    input logic S,
    input logic CLK,
    input logic RST,
    input logic Y
);

    // Active-low reset forces Y low.
    check_reset_clears_y: assert property (
        @(posedge CLK) !RST |-> (Y == 1'b0)
    );

    // When S is low, Y captures A on the next clock.
    check_select_a_capture: assert property (
        @(posedge CLK) disable iff (!RST)
        (S == 1'b0) |=> (Y == $past(A))
    );

    // When S is high, Y captures B on the next clock.
    check_select_b_capture: assert property (
        @(posedge CLK) disable iff (!RST)
        (S == 1'b1) |=> (Y == $past(B))
    );

endmodule