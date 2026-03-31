module counter4_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] count
);

// Reset drives count to zero on the next clock.
    check_reset_clears_count: assert property (
        @(posedge clk) rst |=> (count == 4'b0000)
    );

// Count increments from 0 to 1 when reset is low.
    check_count_0_to_1: assert property (
        @(posedge clk) disable iff (rst) (count == 4'b0000) |=> (count == 4'b0001)
    );

// Count increments from 1 to 2 when reset is low.
    check_count_1_to_2: assert property (
        @(posedge clk) disable iff (rst) (count == 4'b0001) |=> (count == 4'b0010)
    );

// Count increments from 2 to 3 when reset is low.
    check_count_2_to_3: assert property (
        @(posedge clk) disable iff (rst) (count == 4'b0010) |=> (count == 4'b0011)
    );

// Count increments from 3 to 4 when reset is low.
    check_count_3_to_4: assert property (
        @(posedge clk) disable iff (rst) (count == 4'b0011) |=> (count == 4'b0100)
    );

// Count increments from 4 to 5 when reset is low.
    check_count_4_to_5: assert property (
        @(posedge clk) disable iff (rst) (count == 4'b0100) |=> (count == 4'b0101)
    );

// Count increments from 5 to 6 when reset is low.
    check_count_5_to_6: assert property (
        @(posedge clk) disable iff (rst) (count == 4'b0101) |=> (count == 4'b0110)
    );

// Count increments from 6 to 7 when reset is low.
    check_count_6_to_7: assert property (
        @(posedge clk) disable iff (rst) (count == 4'b0110) |=> (count == 4'b0111)
    );

// Count increments from 7 to 8 when reset is low.
    check_count_7_to_8: assert property (
        @(posedge clk) disable iff (rst) (count == 4'b0111) |=> (count == 4'b1000)
    );

// Count increments from 8 to 9 when reset is low.
    check_count_8_to_9: assert property (
        @(posedge clk) disable iff (rst) (count == 4'b1000) |=> (count == 4'b1001)
    );

// Count wraps from 9 back to 0 when reset is low.
    check_count_9_to_0: assert property (
        @(posedge clk) disable iff (rst) (count == 4'b1001) |=> (count == 4'b0000)
    );

endmodule
