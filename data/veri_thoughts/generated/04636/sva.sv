module counter_with_load_sva (
    input logic       clk,
    input logic       load,
    input logic [7:0] data,
    input logic [7:0] count
);

    // Count follows the RTL next-state function on every cycle.
    check_count_transition_relation: assert property (
        @(posedge clk) 1'b1 |=> count == ($past(load) ? $past(data) : ($past(count) + 8'd1))
    );

    // A high load causes count to take the input data.
    check_load_updates_count: assert property (
        @(posedge clk) load |=> count == $past(data)
    );

    // A low load causes count to increment by one.
    check_increment_updates_count: assert property (
        @(posedge clk) !load |=> count == ($past(count) + 8'd1)
    );

    // Incrementing from 8'hFF wraps count back to 8'h00.
    check_increment_wraps_on_overflow: assert property (
        @(posedge clk) (!load && (count == 8'hFF)) |=> count == 8'h00
    );

endmodule