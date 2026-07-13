module shift_register_sva (
    input logic clk,
    input logic d,
    input logic q
);

    // q captures d on the next rising clock edge.
    check_q_captures_d: assert property (
        @(posedge clk) 1'b1 |=> (q == $past(d))
    );

    // A high d is reflected on q one cycle later.
    check_q_sets_after_high_d: assert property (
        @(posedge clk) d |=> q
    );

    // A low d is reflected on q one cycle later.
    check_q_clears_after_low_d: assert property (
        @(posedge clk) !d |=> !q
    );

endmodule