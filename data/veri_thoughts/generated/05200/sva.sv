module fsm_3bit_binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic [2:0] counter
);

    // 000 advances to 001 on the next clock.
    check_count_000_to_001: assert property (
        @(posedge clk) disable iff (reset)
        (counter == 3'b000) |=> (counter == 3'b001)
    );

    // 001 advances to 010 on the next clock.
    check_count_001_to_010: assert property (
        @(posedge clk) disable iff (reset)
        (counter == 3'b001) |=> (counter == 3'b010)
    );

    // 010 advances to 011 on the next clock.
    check_count_010_to_011: assert property (
        @(posedge clk) disable iff (reset)
        (counter == 3'b010) |=> (counter == 3'b011)
    );

    // 011 advances to 100 on the next clock.
    check_count_011_to_100: assert property (
        @(posedge clk) disable iff (reset)
        (counter == 3'b011) |=> (counter == 3'b100)
    );

    // 100 advances to 101 on the next clock.
    check_count_100_to_101: assert property (
        @(posedge clk) disable iff (reset)
        (counter == 3'b100) |=> (counter == 3'b101)
    );

    // 101 advances to 110 on the next clock.
    check_count_101_to_110: assert property (
        @(posedge clk) disable iff (reset)
        (counter == 3'b101) |=> (counter == 3'b110)
    );

    // 110 advances to 111 on the next clock.
    check_count_110_to_111: assert property (
        @(posedge clk) disable iff (reset)
        (counter == 3'b110) |=> (counter == 3'b111)
    );

    // 111 wraps back to 000 on the next clock.
    check_count_111_to_000: assert property (
        @(posedge clk) disable iff (reset)
        (counter == 3'b111) |=> (counter == 3'b000)
    );

endmodule