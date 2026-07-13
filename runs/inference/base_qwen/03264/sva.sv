module up_down_counter_sva (
    input logic clk,
    input logic clear,
    input logic load,
    input logic [3:0] data_in,
    output logic [3:0] count_out
);
    ///// Clear behavior /////
    // When clear is asserted, count_out should be driven to 0.
    clear_behavior: assert property (
        @(posedge clk) disable iff (!clear) count_out == 4'b0
    );

    ///// Load behavior /////
    // When load is asserted, count_out should be driven to data_in.
    load_behavior: assert property (
        @(posedge clk) disable iff (!clear) (load == 1'b1) |-> count_out == data_in
    );

    ///// Up counting behavior /////
    // When up_down is asserted and load is not, count_out should increment.
    up_counting_behavior: assert property (
        @(posedge clk) disable iff (!clear) (up_down == 1'b1) |-> count_out == count_out + 4'b1
    );

    ///// Down counting behavior /////
    // When up_down is not asserted and load is not, count_out should decrement.
    down_counting_behavior: assert property (
        @(posedge clk) disable iff (!clear) (up_down == 1'b0) |-> count_out == count_out - 4'b1
    );

    ///// Count_out should not exceed 4'b1111 or go below 4'b0000 /////
    // Count_out should always be within the valid range.
    count_out_range: assert property (
        @(posedge clk) disable iff (!clear) (count_out >= 4'b0000 && count_out <= 4'b1111)
    );

    ///// Count_out should not change when clear is asserted /////
    // count_out should not change when clear is asserted.
    count_out_clear: assert property (
        @(posedge clk) disable iff (!clear) clear |-> count_out == count_out
    );

    ///// Count_out should not change when load is asserted /////
    // count_out should not change when load is asserted.
    count_out_load: assert property (
        @(posedge clk) disable iff (!clear) load |-> count_out == count_out
    );

    ///// Count_out should not change when up_down is not asserted and load is not asserted /////
    // count_out should not change when up_down is not asserted and load is not asserted.
    count_out_no_change: assert property (
        @(posedge clk) disable iff (!clear) !(up_down == 1'b0 && load == 1'b0) |-> count_out == count_out
    );

    ///// Count_out should not exceed 4'b1111 or go below 4'b0000 when clear is not asserted /////
    // Count_out should always be within the valid range when clear is not asserted.
    count_out_range_no_clear: assert property (
        @(posedge clk) disable iff (clear) (count_out >= 4'b0000 && count_out <= 4'b1111)
    );

    ///// Count_out should not change when clear is not asserted /////
    // count_out should not change when clear is not asserted.
    count_out_no_change_no_clear: assert property (
        @(posedge clk) disable iff (clear) count_out == count_out
    );
endmodule