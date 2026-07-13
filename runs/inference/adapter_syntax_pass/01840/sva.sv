module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic load,
    input logic [3:0] data,
    input logic [3:0] count
);

    // Active-low reset forces count to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !rst |-> (count == 4'h0)
    );

    // A load cycle updates count with data.
    check_load_updates_count: assert property (
        @(posedge clk) disable iff (!rst)
        load |=> (count == $past(data))
    );

    // Without load, count increments by one on the next cycle.
    check_increment_when_not_loading: assert property (
        @(posedge clk) disable iff (!rst)
        !load |=> (count == ($past(count) + 4'h1))
    );

    // The 4-bit counter wraps from 15 back to 0.
    check_count_wraps_from_max: assert property (
        @(posedge clk) disable iff (!rst)
        (!load && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule