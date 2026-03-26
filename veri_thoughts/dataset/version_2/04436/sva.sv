module add_module_assertions (
    input logic clk,
    input logic rst,
    input logic [15:0] in_data,
    input logic [15:0] out_data
);

    // Reset drives the output to zero by the next sampled clock.
    check_reset_clears_out_next: assert property (
        @(posedge clk) !rst |=> (out_data == 16'h0000)
    );

    // While reset stays asserted, the output remains zero.
    check_reset_holds_out_zero: assert property (
        @(posedge clk) (!rst && $past(!rst)) |-> (out_data == 16'h0000)
    );

    // Each active clock loads input plus 16'h1234 into the output register.
    check_active_cycle_updates_sum: assert property (
        @(posedge clk) disable iff (!rst) 1'b1 |=> (out_data == ($past(in_data) + 16'h1234))
    );

    // The first active cycle after reset release also loads the sum correctly.
    check_reset_release_updates_sum: assert property (
        @(posedge clk) disable iff (!rst) !$past(rst) |=> (out_data == ($past(in_data) + 16'h1234))
    );

    // Zero input produces 16'h1234 on the next sampled clock.
    check_zero_input_case: assert property (
        @(posedge clk) disable iff (!rst) (in_data == 16'h0000) |=> (out_data == 16'h1234)
    );

    // Max input wraps around to 16'h1233 on the next sampled clock.
    check_max_input_wraparound: assert property (
        @(posedge clk) disable iff (!rst) (in_data == 16'hFFFF) |=> (out_data == 16'h1233)
    );

endmodule