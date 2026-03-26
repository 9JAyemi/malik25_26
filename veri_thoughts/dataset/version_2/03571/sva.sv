module multiply_subtract_assertions (
    input logic        clk,
    input logic [31:0] data_in,
    input logic [31:0] data_out
);

    // RTL has no clock or reset; clk is used only to sample combinational behavior.

    // Output matches multiply-by-5 followed by subtract-7 modulo 2^32.
    check_functional_relation: assert property (
        @(posedge clk) data_out == (((data_in << 2) + data_in) - 32'd7)
    );

    // A stable input across samples must produce a stable output.
    check_stable_input_gives_stable_output: assert property (
        @(posedge clk) $stable(data_in) |-> $stable(data_out)
    );

    // Zero input produces -7 modulo 2^32.
    check_zero_input_case: assert property (
        @(posedge clk) (data_in == 32'd0) |-> (data_out == 32'hFFFF_FFF9)
    );

    // One input produces -2 modulo 2^32.
    check_one_input_case: assert property (
        @(posedge clk) (data_in == 32'd1) |-> (data_out == 32'hFFFF_FFFE)
    );

    // All-ones input produces 0xFFFF_FFF4 modulo 2^32.
    check_all_ones_input_case: assert property (
        @(posedge clk) (data_in == 32'hFFFF_FFFF) |-> (data_out == 32'hFFFF_FFF4)
    );

endmodule