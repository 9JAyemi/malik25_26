module por_sva (
    input logic        clk,
    input logic        rst,
    input logic [31:0] counter
);

    localparam [31:0] POR_MAX    = 32'h00ffffff;
    localparam [31:0] POR_PREMAX = 32'h00fffffe;

    // Below the terminal count, the counter increments by one.
    check_counter_increments_below_max: assert property (
        @(posedge clk) (counter < POR_MAX) |=> (counter == ($past(counter) + 32'd1))
    );

    // Below the terminal count, rst is asserted on the next cycle.
    check_rst_asserted_below_max: assert property (
        @(posedge clk) (counter < POR_MAX) |=> (rst == 1'b1)
    );

    // At or above the terminal count, the counter stops changing.
    check_counter_holds_at_or_above_max: assert property (
        @(posedge clk) (counter >= POR_MAX) |=> (counter == $past(counter))
    );

    // At or above the terminal count, rst deasserts on the next cycle.
    check_rst_deasserted_at_or_above_max: assert property (
        @(posedge clk) (counter >= POR_MAX) |=> (rst == 1'b0)
    );

    // The final increment reaches the terminal count with rst still high.
    check_transition_into_terminal_count: assert property (
        @(posedge clk) (counter == POR_PREMAX) |=> ((counter == POR_MAX) && (rst == 1'b1))
    );

    // Once sampled at the terminal count, the next cycle stays there with rst low.
    check_terminal_count_behavior: assert property (
        @(posedge clk) (counter == POR_MAX) |=> ((counter == POR_MAX) && (rst == 1'b0))
    );

endmodule