module reg32_async_reset_load_sva (
    input logic        clk,
    input logic        reset,
    input logic        load,
    input logic [31:0] data_in,
    input logic [31:0] data_out
);

    // Active-low reset forces data_out to zero.
    check_reset_clears_data_out: assert property (
        @(posedge clk) !reset |-> (data_out == 32'd0)
    );

    // When load is high, data_out captures data_in on the next registered state.
    check_load_captures_data_in: assert property (
        @(posedge clk) disable iff (!reset) load |=> (data_out == $past(data_in))
    );

    // When load is low, data_out holds its previous value.
    check_no_load_holds_data_out: assert property (
        @(posedge clk) disable iff (!reset) !load |=> (data_out == $past(data_out))
    );

endmodule