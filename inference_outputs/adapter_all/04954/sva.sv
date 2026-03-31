module pipelined_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] OUT
);

    // OUT reflects the sum of A and B from two cycles earlier.
    check_out_two_cycle_latency: assert property (
        @(posedge clk) 1'b1 |-> ##2 (OUT == ($past(A, 2) + $past(B, 2)))
    );

    // If A and B are unchanged over the last two cycles, OUT repeats.
    check_out_repeats_when_inputs_repeat: assert property (
        @(posedge clk) 1'b1 |-> ##2 (($past(A, 2) == $past(A, 3)) && ($past(B, 2) == $past(B, 3))) |-> (OUT == $past(OUT))
    );

    // If A and B are stable over the last two cycles, OUT remains stable.
    check_out_stable_when_inputs_stable: assert property (
        @(posedge clk) 1'b1 |-> ##2 ($stable(A) && $stable(B)) |-> $stable(OUT)
    );

    // If A and B are zero over the last two cycles, OUT is zero.
    check_out_zero_when_inputs_zero: assert property (
        @(posedge clk) 1'b1 |-> ##2 (($past(A, 2) == 4'h0) && ($past(B, 2) == 4'h0)) |-> (OUT == 4'h0)
    );

    // If A and B are 4'hF over the last two cycles, OUT is 4'hE.
    check_out_max_when_inputs_max: assert property (
        @(posedge clk) 1'b1 |-> ##2 (($past(A, 2) == 4'hF) && ($past(B, 2) == 4'hF)) |-> (OUT == 4'hE)
    );

endmodule