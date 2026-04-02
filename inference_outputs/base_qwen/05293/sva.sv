module sync_counter_sva(
    input logic clk,
    input logic rst,
    input logic load,
    input logic [3:0] data,
    input logic [3:0] count
);
    ///// Reset behavior /////
    // At reset, count should be driven to 0.
    reset: assert property (
        @(posedge clk) disable iff (!rst) count == 4'b0
    );

    ///// Load behavior /////
    // When load is asserted, count should be driven to the value of data.
    load_behavior: assert property (
        @(posedge clk) disable iff (!rst) (load |-> count == data)
    );

    ///// Count increment behavior /////
    // When load is not asserted, count should increment by 1.
    increment_behavior: assert property (
        @(posedge clk) disable iff (!rst) (!load |-> count == count + 1)
    );

    ///// Count range behavior /////
    // Count should not exceed 4'b1111.
    count_range: assert property (
        @(posedge clk) disable iff (!rst) count <= 4'b1111
    );

    ///// Count underflow behavior /////
    // Count should not go below 4'b0000.
    count_underflow: assert property (
        @(posedge clk) disable iff (!rst) count >= 4'b0000
    );

    ///// Load and count increment cannot happen at the same time /////
    // Load and count increment cannot happen simultaneously.
    load_and_increment: assert property (
        @(posedge clk) disable iff (!rst) !(load & !count == count + 1)
    );

    ///// Count should not change when reset is asserted /////
    // Count should not change when reset is asserted.
    count_during_reset: assert property (
        @(posedge clk) disable iff (rst) count == count
    );

    ///// Load should not change when reset is asserted /////
    // Load should not change when reset is asserted.
    load_during_reset: assert property (
        @(posedge clk) disable iff (rst) load == load
    );

    ///// Data should not change when reset is asserted /////
    // Data should not change when reset is asserted.
    data_during_reset: assert property (
        @(posedge clk) disable iff (rst) data == data
    );

    ///// Count should not change when load is asserted /////
    // Count should not change when load is asserted.
    count_during_load: assert property (
        @(posedge clk) disable iff (load) count == count
    );
endmodule