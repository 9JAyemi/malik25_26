module alu_sva (
    input logic [3:0] data1,
    input logic [3:0] data2,
    input logic [1:0] op,
    input logic [3:0] q,
    input logic clk
);

    // q reflects the add result from two cycles earlier.
    check_q_add_two_cycle_latency: assert property (
        @(posedge clk)
        (op == 2'b00) |-> ##2 (q == (($past(data1, 2) + $past(data2, 2)) & 4'hF))
    );

    // q reflects the subtract result from two cycles earlier.
    check_q_sub_two_cycle_latency: assert property (
        @(posedge clk)
        (op == 2'b01) |-> ##2 (q == (($past(data1, 2) - $past(data2, 2)) & 4'hF))
    );

    // q reflects the bitwise AND result from two cycles earlier.
    check_q_and_two_cycle_latency: assert property (
        @(posedge clk)
        (op == 2'b10) |-> ##2 (q == ($past(data1, 2) & $past(data2, 2)))
    );

    // q reflects the bitwise OR result from two cycles earlier.
    check_q_or_two_cycle_latency: assert property (
        @(posedge clk)
        (op == 2'b11) |-> ##2 (q == ($past(data1, 2) | $past(data2, 2)))
    );

    // q always matches the operation selected two cycles earlier.
    check_q_matches_selected_operation: assert property (
        @(posedge clk)
        1'b1 |-> ##2 (
            q == (
                ($past(op, 2) == 2'b00) ? ((($past(data1, 2) + $past(data2, 2)) & 4'hF)) :
                ($past(op, 2) == 2'b01) ? ((($past(data1, 2) - $past(data2, 2)) & 4'hF)) :
                ($past(op, 2) == 2'b10) ? (($past(data1, 2) & $past(data2, 2))) :
                                          (($past(data1, 2) | $past(data2, 2)))
            )
        )
    );

endmodule