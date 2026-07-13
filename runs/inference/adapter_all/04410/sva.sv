module fifo_buffer_sva #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 4
) (
    input logic clk,
    input logic aclr,
    input logic [DATA_WIDTH-1:0] din,
    input logic [DATA_WIDTH-1:0] dout,
    input logic [DATA_WIDTH-1:0] mem [DEPTH-1:0]
);

    // Reset clears the entire memory and the output.
    check_reset_clears_memory_and_dout: assert property (
        @(posedge clk) aclr |-> ((mem == '{DEPTH{DATA_WIDTH{1'b0}}}) && (dout == {DATA_WIDTH{1'b0}}))
    );

    // Reset also clears the internal temp register.
    check_reset_clears_temp: assert property (
        @(posedge clk) aclr |-> ((temp == {DATA_WIDTH{1'b0}}))
    );

    // The output reflects the oldest memory entry after reset.
    check_dout_matches_oldest_memory_after_reset: assert property (
        @(posedge clk) aclr |-> (dout == mem[DEPTH-1])
    );

    // The first memory entry captures the input when not in reset.
    check_first_memory_captures_din: assert property (
        @(posedge clk) disable iff (aclr) (mem[0] == din)
    );

    // Each non-reset cycle shifts the memory down by one.
    check_memory_shifts_on_each_cycle: assert property (
        @(posedge clk) disable iff (aclr) (mem == $past(mem, 1, aclr, 1'b1, DEPTH))
    );

    // The output reflects the oldest memory entry after each non-reset cycle.
    check_dout_matches_oldest_memory: assert property (
        @(posedge clk) disable iff (aclr) (dout == mem[DEPTH-1])
    );

    // The output is the delayed input value after the appropriate latency.
    check_dout_matches_delayed_din: assert property (
        @(posedge clk) disable iff (aclr) (dout == $past(din, DEPTH, aclr, 1'b1, DATA_WIDTH))
    );

endmodule