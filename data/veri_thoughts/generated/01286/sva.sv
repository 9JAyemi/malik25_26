module shift_register_parallel_load_sva (
    input logic clk,
    input logic rst,     // active-high reset
    input logic load,
    input logic [7:0] in,
    input logic [7:0] out
);
    // Reset forces output to zero.
    check_reset_clears_out: assert property (
        @(posedge clk) rst |-> (out == 8'b0)
    );

    // Load writes input to output on the same cycle when not in reset.
    check_load_parallel_load: assert property (
        @(posedge clk) disable iff (rst) load |-> (out == in)
    );

    // When shifting (no load), LSB becomes 0.
    check_shift_lsb_zero: assert property (
        @(posedge clk) disable iff (rst) !load |-> (out[0] == 1'b0)
    );

    // With no load, once out is zero it stays zero.
    check_no_load_zero_stays_zero: assert property (
        @(posedge clk) disable iff (rst) (!load && $past(1'b1) && ($past(out) == 8'b0)) |-> (out == 8'b0)
    );

    // After two consecutive no-load cycles, lower 2 bits are zero.
    check_two_no_loads_zero_low2: assert property (
        @(posedge clk) disable iff (rst) (!load)[*2] |-> (out[1:0] == 2'b00)
    );

    // After four consecutive no-load cycles, lower 4 bits are zero.
    check_four_no_loads_zero_low4: assert property (
        @(posedge clk) disable iff (rst) (!load)[*4] |-> (out[3:0] == 4'b0000)
    );

    // After eight consecutive no-load cycles, output is zero.
    check_eight_no_loads_clears_out: assert property (
        @(posedge clk) disable iff (rst) (!load)[*8] |-> (out == 8'b00000000)
    );

    // Loading zero drives output to zero.
    check_load_zero_clears_out: assert property (
        @(posedge clk) disable iff (rst) (load && (in == 8'b0)) |-> (out == 8'b0)
    );

    // On load, LSB of output equals LSB of input.
    check_load_lsb_transfer: assert property (
        @(posedge clk) disable iff (rst) load |-> (out[0] == in[0])
    );

    // On sampled rising edge of reset, output is zero.
    check_reset_rise_clears_out: assert property (
        @(posedge clk) $rose(rst) |-> (out == 8'b0)
    );
endmodule