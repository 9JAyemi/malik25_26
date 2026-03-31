module johnson_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [2:0] out
);

    // Reset drives the registered output to 000 on the next cycle.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |=> (out == 3'b000)
    );

    // 000 rotates back to 000 in normal operation.
    check_state_000_to_000: assert property (
        @(posedge clk) disable iff (reset) (out == 3'b000) |=> (out == 3'b000)
    );

    // 001 rotates to 010 in normal operation.
    check_state_001_to_010: assert property (
        @(posedge clk) disable iff (reset) (out == 3'b001) |=> (out == 3'b010)
    );

    // 010 rotates to 100 in normal operation.
    check_state_010_to_100: assert property (
        @(posedge clk) disable iff (reset) (out == 3'b010) |=> (out == 3'b100)
    );

    // 011 rotates to 110 in normal operation.
    check_state_011_to_110: assert property (
        @(posedge clk) disable iff (reset) (out == 3'b011) |=> (out == 3'b110)
    );

    // 100 rotates to 001 in normal operation.
    check_state_100_to_001: assert property (
        @(posedge clk) disable iff (reset) (out == 3'b100) |=> (out == 3'b001)
    );

    // 101 rotates to 011 in normal operation.
    check_state_101_to_011: assert property (
        @(posedge clk) disable iff (reset) (out == 3'b101) |=> (out == 3'b011)
    );

    // 110 rotates to 101 in normal operation.
    check_state_110_to_101: assert property (
        @(posedge clk) disable iff (reset) (out == 3'b110) |=> (out == 3'b101)
    );

    // 111 rotates back to 111 in normal operation.
    check_state_111_to_111: assert property (
        @(posedge clk) disable iff (reset) (out == 3'b111) |=> (out == 3'b111)
    );

endmodule