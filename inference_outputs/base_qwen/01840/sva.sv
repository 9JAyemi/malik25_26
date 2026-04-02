module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic load,
    input logic [3:0] data,
    input logic [3:0] count
);
    ///// Reset behavior /////
    // At reset, count must be driven to 0.
    reset: assert property (
        @(posedge clk) !rst |-> (count == 4'b0)
    );

    ///// Load behavior /////
    // When load is asserted, count must be driven to the value of data.
    load_behavior: assert property (
        @(posedge clk) disable iff (!rst) load |-> (count == data)
    );

    ///// Count increment behavior /////
    // When load is not asserted, count must increment by 1 on each clock edge.
    increment_behavior: assert property (
        @(posedge clk) disable iff (!rst) !load |-> (count == count + 4'b1)
    );

    ///// Count rollover behavior /////
    // When count reaches 4'b1111, it should rollover to 4'b0000.
    rollover_behavior: assert property (
        @(posedge clk) disable iff (!rst) count == 4'b1111 |-> (count == 4'b0000)
    );

    ///// Count should not be greater than 4'b1111 /////
    // Count should always be between 0 and 15.
    count_range: assert property (
        @(posedge clk) disable iff (!rst) count inside {[0:15]}
    );

    ///// Load should not be asserted when count is not 0 /////
    // Load should only be asserted when count is 0.
    load_when_count_zero: assert property (
        @(posedge clk) disable iff (!rst) count != 4'b0000 |-> !load
    );

    ///// Count should not increment when load is asserted /////
    // Count should not increment when load is asserted.
    count_not_increment_on_load: assert property (
        @(posedge clk) disable iff (!rst) load |-> count == count
    );

    ///// Count should not be greater than data when load is asserted /////
    // When load is asserted, count should be equal to data.
    count_not_greater_than_data_on_load: assert property (
        @(posedge clk) disable iff (!rst) load |-> count == data
    );

    ///// Count should not be less than data when load is not asserted /////
    // When load is not asserted, count should be greater than or equal to data.
    count_not_less_than_data_on_not_load: assert property (
        @(posedge clk) disable iff (!rst) !load |-> count >= data
    );

    ///// Count should not be equal to data when load is not asserted /////
    // When load is not asserted, count should not be equal to data.
    count_not_equal_to_data_on_not_load: assert property (
        @(posedge clk) disable iff (!rst) !load |-> count != data
    );
endmodule