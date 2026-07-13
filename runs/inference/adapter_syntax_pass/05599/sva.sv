module rotation_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] in,
    input logic load,
    input logic select,
    input logic [15:0] data,
    input logic [3:0] out
);

    // Reset forces the output to zero.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |-> (out == 4'b0000)
    );

    // Load captures the low 4 bits of data.
    check_load_captures_data: assert property (
        @(posedge clk) disable iff (reset)
        load |=> (out == $past(data[3:0]))
    );

    // Load has priority over select.
    check_load_priority_over_select: assert property (
        @(posedge clk) disable iff (reset)
        (load && select) |=> (out == $past(data[3:0]))
    );

    // Select rotates in left-to-right when load is low.
    check_select_rotates_left: assert property (
        @(posedge clk) disable iff (reset)
        (!load && select) |=> (out == {$past(in[2:0]), $past(in[3])})
    );

    // Without load or select, the output rotates in right-to-left.
    check_default_rotates_right: assert property (
        @(posedge clk) disable iff (reset)
        (!load && !select) |=> (out == {$past(in[0]), $past(in[3:1])})
    );

endmodule