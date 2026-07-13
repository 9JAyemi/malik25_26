module UniversalCounter8bits_sva (
    input logic CLOCK,
    input logic Reset,
    input logic S1,
    input logic S0,
    input logic [7:0] P,
    input logic [7:0] BeginCount,
    input logic [7:0] EndCount,
    input logic [7:0] Q,
    input logic TerminalCount
);

    // Reset drives the outputs to zero by the next clock sample.
    check_reset_clears_outputs: assert property (
        @(posedge CLOCK)
        Reset |=> (Q == 8'd0 && TerminalCount == 1'b0)
    );

    // Hold mode keeps Q unchanged and clears TerminalCount.
    check_hold_mode: assert property (
        @(posedge CLOCK) disable iff (Reset)
        ({S1, S0} == 2'b00) |=> (Q == $past(Q) && TerminalCount == 1'b0)
    );

    // Count-up mode increments Q when it is not at EndCount.
    check_count_up_increment: assert property (
        @(posedge CLOCK) disable iff (Reset)
        ({S1, S0} == 2'b01 && Q != EndCount) |=> (Q == ($past(Q) + 8'd1) && TerminalCount == 1'b0)
    );

    // Count-up mode wraps to BeginCount and raises TerminalCount at EndCount.
    check_count_up_wrap: assert property (
        @(posedge CLOCK) disable iff (Reset)
        ({S1, S0} == 2'b01 && Q == EndCount) |=> (Q == $past(BeginCount) && TerminalCount == 1'b1)
    );

    // Count-down mode decrements Q when it is not at BeginCount.
    check_count_down_decrement: assert property (
        @(posedge CLOCK) disable iff (Reset)
        ({S1, S0} == 2'b10 && Q != BeginCount) |=> (Q == ($past(Q) - 8'd1) && TerminalCount == 1'b0)
    );

    // Count-down mode wraps to EndCount and raises TerminalCount at BeginCount.
    check_count_down_wrap: assert property (
        @(posedge CLOCK) disable iff (Reset)
        ({S1, S0} == 2'b10 && Q == BeginCount) |=> (Q == $past(EndCount) && TerminalCount == 1'b1)
    );

    // Parallel load mode loads P into Q and clears TerminalCount.
    check_parallel_load: assert property (
        @(posedge CLOCK) disable iff (Reset)
        ({S1, S0} == 2'b11) |=> (Q == $past(P) && TerminalCount == 1'b0)
    );

endmodule