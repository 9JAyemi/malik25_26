module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [35:0] in,
    input logic [31:0] out
);

// Reset clears the output on the next clock.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |=> (out == 32'h0)
    );

// Upper 32 bits of out are zeroed by the functional module.
    check_out_upper_zero: assert property (
        @(posedge clk) disable iff (reset) (out[31:4] == 28'h0)
    );

// Lower 4 bits of out are zeroed by the functional module.
    check_out_lower_zero: assert property (
        @(posedge clk) disable iff (reset) (out[3:0] == 4'h0)
    );

// A change on the upper 32-bit input path sets the upper 28 bits of out.
    check_change_upper_sets_bits: assert property (
        @(posedge clk) disable iff (reset)
            $changed(in[35:4]) |=> (out[31:4] == 28'h0FFFF_FFFF)
    );

// A change on the lower 4-bit input path sets the lower 4 bits of out.
    check_change_lower_sets_bits: assert property (
        @(posedge clk) disable iff (reset)
            $changed(in[3:0]) |=> (out[3:0] == 4'hF)
    );

// No change on the upper 32-bit input path clears the upper 28 bits of out.
    check_no_change_upper_clears_bits: assert property (
        @(posedge clk) disable iff (reset)
            !$changed(in[35:4]) |=> (out[31:4] == 28'h0)
    );

// No change on the lower 4-bit input path clears the lower 4 bits of out.
    check_no_change_lower_clears_bits: assert property (
        @(posedge clk) disable iff (reset)
            !$changed(in[3:0]) |=> (out[3:0] == 4'h0)
    );

endmodule
