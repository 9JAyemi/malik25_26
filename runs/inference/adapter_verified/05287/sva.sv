module sqrt_calc_sva (
    input logic clk,
    input logic [7:0] x,
    input logic [7:0] y
);

// Output is always zero when input is zero.
    check_zero_input_zero_output: assert property (
        @(posedge clk) (x == 8'h00) |-> (y == 8'h00)
    );

// Output is always zero when input is less than 4.
    check_small_input_zero_output: assert property (
        @(posedge clk) (x < 8'h04) |-> (y == 8'h00)
    );

// Output is always zero when input is less than 16.
    check_quarter_input_zero_output: assert property (
        @(posedge clk) (x < 8'h10) |-> (y == 8'h00)
    );

// Output is always zero when input is less than 32.
    check_half_input_zero_output: assert property (
        @(posedge clk) (x < 8'h20) |-> (y == 8'h00)
    );

// Output is always zero when input is less than 64.
    check_three_quarter_input_zero_output: assert property (
        @(posedge clk) (x < 8'h40) |-> (y == 8'h00)
    );

// Output is always zero when input is less than 128.
    check_full_input_zero_output: assert property (
        @(posedge clk) (x < 8'h80) |-> (y == 8'h00)
    );

// Output is always zero when input is less than 256.
    check_two_byte_input_zero_output: assert property (
        @(posedge clk) (x < 8'hFF) |-> (y == 8'h00)
    );

// Output is always zero when input is less than 512.
    check_half_byte_input_zero_output: assert property (
        @(posedge clk) (x < 8'hFF) |-> (y == 8'h00)
    );

// Output is always zero when input is less than 1024.
    check_full_byte_input_zero_output: assert property (
        @(posedge clk) (x < 8'hFF) |-> (y == 8'h00)
    );

endmodule
