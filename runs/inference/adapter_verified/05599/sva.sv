module rotation_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] in,
    input logic load,
    input logic select,
    input logic [15:0] data,
    input logic [3:0] out
);

// Reset clears the output on the next clock.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |=> (out == 4'b0000)
    );

// Load captures the low nibble of data when select is low.
    check_load_captures_data_low_nibble: assert property (
        @(posedge clk) disable iff (reset)
        (load && !select) |=> (out == data[3:0])
    );

// Load has priority over select when both are high.
    check_load_priority_over_select: assert property (
        @(posedge clk) disable iff (reset)
        (load && select) |=> (out == data[3:0])
    );

// Select rotates in left when load is low and select is high.
    check_select_rotates_left: assert property (
        @(posedge clk) disable iff (reset)
        (!load && select) |=> (out == {in[2:0], in[3]})
    );

// Without load or select, the output rotates right by one bit.
    check_default_rotates_right: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !select) |=> (out == {in[0], in[3:1]})
    );

endmodule
