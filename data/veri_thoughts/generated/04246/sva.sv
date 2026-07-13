module johnson_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [2:0] count
);

    // A sampled reset drives the counter to 000 on the following clock.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 3'b000)
    );

    // Outside reset, the next count follows the Johnson update function.
    check_next_state_relation: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (count == {$past(count[1:0]), ~$past(count[2])})
    );

    // State 000 advances to 001.
    check_state_000_to_001: assert property (
        @(posedge clk) disable iff (reset)
        (count == 3'b000) |=> (count == 3'b001)
    );

    // State 001 advances to 011.
    check_state_001_to_011: assert property (
        @(posedge clk) disable iff (reset)
        (count == 3'b001) |=> (count == 3'b011)
    );

    // State 011 advances to 111.
    check_state_011_to_111: assert property (
        @(posedge clk) disable iff (reset)
        (count == 3'b011) |=> (count == 3'b111)
    );

    // State 111 advances to 110.
    check_state_111_to_110: assert property (
        @(posedge clk) disable iff (reset)
        (count == 3'b111) |=> (count == 3'b110)
    );

    // State 110 advances to 100.
    check_state_110_to_100: assert property (
        @(posedge clk) disable iff (reset)
        (count == 3'b110) |=> (count == 3'b100)
    );

    // State 100 advances to 000.
    check_state_100_to_000: assert property (
        @(posedge clk) disable iff (reset)
        (count == 3'b100) |=> (count == 3'b000)
    );

endmodule