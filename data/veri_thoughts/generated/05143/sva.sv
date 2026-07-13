module DFF_sva (
    input logic clk,
    input logic d,
    input logic q
);

    // Q reflects D from the previous rising clock edge.
    check_q_captures_previous_d: assert property (
        @(posedge clk) 1'b1 |=> (q == $past(d))
    );

    // If D matches Q at a clock edge, Q holds its value on the next edge.
    check_q_holds_when_d_matches_q: assert property (
        @(posedge clk) (d == q) |=> (q == $past(q))
    );

    // If D differs from Q at a clock edge, Q changes on the next edge.
    check_q_changes_when_d_differs: assert property (
        @(posedge clk) (d != q) |=> (q != $past(q))
    );

endmodule