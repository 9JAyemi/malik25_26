module simple_adder_sva (
    input logic clk,
    input logic rst,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C
);

    // Reset clears C on the next clock.
    check_reset_clears_c: assert property (
        @(posedge clk) rst |=> (C == 8'h00)
    );

    // Outside reset, C captures the previous cycle's A+B.
    check_c_captures_sum: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (C == ($past(A) + $past(B)))
    );

    // Outside reset, C is always the previous cycle's A+B.
    check_c_matches_previous_sum: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> (C == ($past(A) + $past(B)))
    );

endmodule