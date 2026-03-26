module binary_counter_sva(
    input logic clk,
    input logic rst,
    input logic [2:0] count
);

    // Reset clears count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 3'b000)
    );

    // Count increments from 0 to 1.
    check_count_0_to_1: assert property (
        @(posedge clk) disable iff (rst)
        (count == 3'b000) |=> (count == 3'b001)
    );

    // Count increments from 1 to 2.
    check_count_1_to_2: assert property (
        @(posedge clk) disable iff (rst)
        (count == 3'b001) |=> (count == 3'b010)
    );

    // Count increments from 2 to 3.
    check_count_2_to_3: assert property (
        @(posedge clk) disable iff (rst)
        (count == 3'b010) |=> (count == 3'b011)
    );

    // Count increments from 3 to 4.
    check_count_3_to_4: assert property (
        @(posedge clk) disable iff (rst)
        (count == 3'b011) |=> (count == 3'b100)
    );

    // Count increments from 4 to 5.
    check_count_4_to_5: assert property (
        @(posedge clk) disable iff (rst)
        (count == 3'b100) |=> (count == 3'b101)
    );

    // Count increments from 5 to 6.
    check_count_5_to_6: assert property (
        @(posedge clk) disable iff (rst)
        (count == 3'b101) |=> (count == 3'b110)
    );

    // Count increments from 6 to 7.
    check_count_6_to_7: assert property (
        @(posedge clk) disable iff (rst)
        (count == 3'b110) |=> (count == 3'b111)
    );

    // Count wraps from 7 to 0.
    check_count_7_to_0: assert property (
        @(posedge clk) disable iff (rst)
        (count == 3'b111) |=> (count == 3'b000)
    );

endmodule