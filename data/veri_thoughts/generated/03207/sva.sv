module top_module_sva (
    input logic        clk,
    input logic [15:0] in1,
    input logic [15:0] in2,
    input logic [3:0]  shift_amt,
    input logic        shift_dir,
    input logic [15:0] out
);

    // Left-shift mode outputs the 16-bit sum shifted left by shift_amt.
    check_left_shift_result: assert property (
        @(posedge clk)
        shift_dir |-> (out == ((in1 + in2) << shift_amt))
    );

    // Right-shift mode outputs the 16-bit sum shifted right by shift_amt.
    check_right_shift_result: assert property (
        @(posedge clk)
        !shift_dir |-> (out == ((in1 + in2) >> shift_amt))
    );

    // A zero shift leaves the 16-bit adder result unchanged.
    check_zero_shift_passthrough: assert property (
        @(posedge clk)
        (shift_amt == 4'd0) |-> (out == (in1 + in2))
    );

    // Left shifts fill the vacated low bits with zeros.
    check_left_shift_zero_fill_low: assert property (
        @(posedge clk)
        shift_dir |-> ((out & ~(16'hFFFF << shift_amt)) == 16'h0000)
    );

    // Right shifts fill the vacated high bits with zeros.
    check_right_shift_zero_fill_high: assert property (
        @(posedge clk)
        !shift_dir |-> ((out & ~(16'hFFFF >> shift_amt)) == 16'h0000)
    );

endmodule