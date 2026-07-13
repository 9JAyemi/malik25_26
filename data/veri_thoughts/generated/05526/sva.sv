module adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic RESET_B,
    input logic CLK,
    input logic [3:0] SUM
);

    // A low RESET_B on a clock edge forces SUM to zero on the next cycle.
    check_reset_clears_sum: assert property (
        @(posedge CLK) !RESET_B |=> (SUM == 4'b0000)
    );

    // In normal operation, SUM reflects the previous cycle's A+B result.
    check_sum_updates_from_inputs: assert property (
        @(posedge CLK) disable iff (!RESET_B || $initstate)
        $past(RESET_B) |-> (SUM == $past(A + B))
    );

endmodule