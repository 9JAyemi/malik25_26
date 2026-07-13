module binary_counter_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic [2:0] count
);

    // Reset clears the counter by the next clock sample.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 3'b000)
    );

    // When disabled, the counter holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !enable |=> $stable(count)
    );

    // When enabled from 0, the counter increments to 1.
    check_increment_000_to_001: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count == 3'b000) |=> (count == 3'b001)
    );

    // When enabled from 1, the counter increments to 2.
    check_increment_001_to_010: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count == 3'b001) |=> (count == 3'b010)
    );

    // When enabled from 2, the counter increments to 3.
    check_increment_010_to_011: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count == 3'b010) |=> (count == 3'b011)
    );

    // When enabled from 3, the counter increments to 4.
    check_increment_011_to_100: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count == 3'b011) |=> (count == 3'b100)
    );

    // When enabled from 4, the counter increments to 5.
    check_increment_100_to_101: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count == 3'b100) |=> (count == 3'b101)
    );

    // When enabled from 5, the counter increments to 6.
    check_increment_101_to_110: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count == 3'b101) |=> (count == 3'b110)
    );

    // When enabled from 6, the counter increments to 7.
    check_increment_110_to_111: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count == 3'b110) |=> (count == 3'b111)
    );

    // When enabled from 7, the counter wraps to 0.
    check_increment_111_to_000: assert property (
        @(posedge clk) disable iff (reset)
        enable && (count == 3'b111) |=> (count == 3'b000)
    );

endmodule