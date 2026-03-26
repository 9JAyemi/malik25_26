module counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [2:0] count
);

    // Held reset keeps count at zero.
    check_reset_holds_zero: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (count == 3'd0)
    );

    // Reset release leaves count at zero before counting resumes.
    check_reset_release_leaves_zero: assert property (
        @(posedge clk) (!rst && $past(rst)) |-> (count == 3'd0)
    );

    // Count increments from 0 to 1.
    check_count_0_to_1: assert property (
        @(posedge clk) disable iff (rst) (count == 3'd0) |=> (count == 3'd1)
    );

    // Count increments from 1 to 2.
    check_count_1_to_2: assert property (
        @(posedge clk) disable iff (rst) (count == 3'd1) |=> (count == 3'd2)
    );

    // Count increments from 2 to 3.
    check_count_2_to_3: assert property (
        @(posedge clk) disable iff (rst) (count == 3'd2) |=> (count == 3'd3)
    );

    // Count increments from 3 to 4.
    check_count_3_to_4: assert property (
        @(posedge clk) disable iff (rst) (count == 3'd3) |=> (count == 3'd4)
    );

    // Count increments from 4 to 5.
    check_count_4_to_5: assert property (
        @(posedge clk) disable iff (rst) (count == 3'd4) |=> (count == 3'd5)
    );

    // Count increments from 5 to 6.
    check_count_5_to_6: assert property (
        @(posedge clk) disable iff (rst) (count == 3'd5) |=> (count == 3'd6)
    );

    // Count increments from 6 to 7.
    check_count_6_to_7: assert property (
        @(posedge clk) disable iff (rst) (count == 3'd6) |=> (count == 3'd7)
    );

    // Count wraps from 7 back to 0.
    check_count_7_to_0: assert property (
        @(posedge clk) disable iff (rst) (count == 3'd7) |=> (count == 3'd0)
    );

endmodule