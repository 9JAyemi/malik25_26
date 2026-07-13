module sumwrap_uint16_to1_1_sva (
    input logic        CLK,
    input logic        CE,
    input logic [31:0] process_input,
    input logic [15:0] process_output
);

    wire [15:0] least_sig_bits;
    wire [15:0] most_sig_bits;

    assign least_sig_bits = process_input[15:0];
    assign most_sig_bits  = process_input[31:16];

    // Output matches the implemented ternary function.
    check_output_function: assert property (
        @(posedge CLK)
        process_output == ((least_sig_bits == 16'd1) ? 16'd0 : (least_sig_bits + most_sig_bits))
    );

    // A lower half of 1 forces the output to zero.
    check_lsb_one_forces_zero: assert property (
        @(posedge CLK)
        (least_sig_bits == 16'd1) |-> (process_output == 16'd0)
    );

    // Any other lower half produces the sum of the two halves.
    check_non_one_lsb_sums_halves: assert property (
        @(posedge CLK)
        (least_sig_bits != 16'd1) |-> (process_output == (least_sig_bits + most_sig_bits))
    );

    // A zero lower half passes the upper half through to the output.
    check_zero_lsb_passes_upper: assert property (
        @(posedge CLK)
        (least_sig_bits == 16'd0) |-> (process_output == most_sig_bits)
    );

    // A zero upper half passes the lower half through unless the lower half is 1.
    check_zero_msb_passes_lower: assert property (
        @(posedge CLK)
        ((most_sig_bits == 16'd0) && (least_sig_bits != 16'd1)) |-> (process_output == least_sig_bits)
    );

    // An all-zero input produces an all-zero output.
    check_zero_input_zero_output: assert property (
        @(posedge CLK)
        (process_input == 32'd0) |-> (process_output == 16'd0)
    );

endmodule