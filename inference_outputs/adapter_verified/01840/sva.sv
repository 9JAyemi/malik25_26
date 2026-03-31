module binary_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic       load,
    input logic [3:0] data,
    input logic [3:0] count
);

// Active-low reset clears the counter to zero.
    check_reset_clears_count: assert property (
        @(posedge clk) !rst |-> (count == 4'b0000)
    );

// A load cycle captures data into the counter.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (!rst)
        load |=> (count == $past(data))
    );

// Without load, the counter increments by one on the next cycle.
    check_increment_when_not_loading: assert property (
        @(posedge clk) disable iff (!rst)
        !load |=> (count == ($past(count) + 4'd1))
    );

// Incrementing from 4'hF wraps the counter to zero.
    check_increment_wraps_from_max: assert property (
        @(posedge clk) disable iff (!rst)
        (!load && (count == 4'hF)) |=> (count == 4'h0)
    );

endmodule
