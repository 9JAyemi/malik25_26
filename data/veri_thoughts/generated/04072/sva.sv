module calculator_sva (
    input logic       clk,
    input logic       rst,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic       op,
    input logic [7:0] result
);

    // A sampled reset cycle leaves result cleared through the next clock edge.
    check_reset_clears_result: assert property (
        @(posedge clk) rst |=> (result == 8'h00)
    );

    // When add is selected, result updates to the prior cycle's a + b.
    check_add_result: assert property (
        @(posedge clk) disable iff (rst)
        (op == 1'b0) |=> (result == ($past(a) + $past(b)))
    );

    // When subtract is selected, result updates to the prior cycle's a - b.
    check_sub_result: assert property (
        @(posedge clk) disable iff (rst)
        (op == 1'b1) |=> (result == ($past(a) - $past(b)))
    );

endmodule