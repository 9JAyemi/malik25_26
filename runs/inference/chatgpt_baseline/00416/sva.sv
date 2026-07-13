module shift_register_sva (
    input logic clk,
    input logic d,
    input logic q
);

    // q captures a 1 from d on the following clock edge.
    check_q_captures_high_d: assert property (
        @(posedge clk) d |=> q
    );

    // q captures a 0 from d on the following clock edge.
    check_q_captures_low_d: assert property (
        @(posedge clk) !d |=> !q
    );

endmodule