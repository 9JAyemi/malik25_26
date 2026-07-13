module binary_counter_sva(
    input logic       clk,
    input logic       reset,
    input logic [2:0] count
);

    // Reset clears the counter on the next clock edge.
    check_reset_clears_count: assert property (
        @(posedge clk) reset |=> (count == 3'b000)
    );

    // Count advances from 0 to 1 when not in reset.
    check_count_0_to_1: assert property (
        @(posedge clk) disable iff (reset)
        (count == 3'b000) |=> (count == 3'b001)
    );

    // Count advances from 1 to 2 when not in reset.
    check_count_1_to_2: assert property (
        @(posedge clk) disable iff (reset)
        (count == 3'b001) |=> (count == 3'b010)
    );

    // Count advances from 2 to 3 when not in reset.
    check_count_2_to_3: assert property (
        @(posedge clk) disable iff (reset)
        (count == 3'b010) |=> (count == 3'b011)
    );

    // Count advances from 3 to 4 when not in reset.
    check_count_3_to_4: assert property (
        @(posedge clk) disable iff (reset)
        (count == 3'b011) |=> (count == 3'b100)
    );

    // Count advances from 4 to 5 when not in reset.
    check_count_4_to_5: assert property (
        @(posedge clk) disable iff (reset)
        (count == 3'b100) |=> (count == 3'b101)
    );

    // Count advances from 5 to 6 when not in reset.
    check_count_5_to_6: assert property (
        @(posedge clk) disable iff (reset)
        (count == 3'b101) |=> (count == 3'b110)
    );

    // Count advances from 6 to 7 when not in reset.
    check_count_6_to_7: assert property (
        @(posedge clk) disable iff (reset)
        (count == 3'b110) |=> (count == 3'b111)
    );

    // Count wraps from 7 back to 0 when not in reset.
    check_count_7_to_0: assert property (
        @(posedge clk) disable iff (reset)
        (count == 3'b111) |=> (count == 3'b000)
    );

endmodule