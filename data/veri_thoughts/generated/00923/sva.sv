module binary_converter_sva (
    input logic clk,
    input logic [3:0] binary_in,
    input logic [1:0] binary_out
);
    // Out[0] must be 1 when input >= 5.
    check_out0_high_when_ge5: assert property (
        @(posedge clk) (binary_in >= 4'd5) |-> (binary_out[0] == 1'b1)
    );

    // Out[0] must be 0 when input < 5.
    check_out0_low_when_lt5: assert property (
        @(posedge clk) (binary_in < 4'd5) |-> (binary_out[0] == 1'b0)
    );

    // Out[0] == 1 implies input >= 5.
    check_out0_implies_ge5: assert property (
        @(posedge clk) (binary_out[0] == 1'b1) |-> (binary_in >= 4'd5)
    );

    // Out[0] == 0 implies input < 5.
    check_out0_zero_implies_lt5: assert property (
        @(posedge clk) (binary_out[0] == 1'b0) |-> (binary_in < 4'd5)
    );

    // Out[1] must be 1 when LSB of input is 1.
    check_out1_high_when_odd: assert property (
        @(posedge clk) (binary_in[0] == 1'b1) |-> (binary_out[1] == 1'b1)
    );

    // Out[1] must be 0 when LSB of input is 0.
    check_out1_low_when_even: assert property (
        @(posedge clk) (binary_in[0] == 1'b0) |-> (binary_out[1] == 1'b0)
    );

    // Out[1] == 1 implies LSB of input is 1.
    check_out1_implies_lsb1: assert property (
        @(posedge clk) (binary_out[1] == 1'b1) |-> (binary_in[0] == 1'b1)
    );

    // Out[1] == 0 implies LSB of input is 0.
    check_out1_zero_implies_lsb0: assert property (
        @(posedge clk) (binary_out[1] == 1'b0) |-> (binary_in[0] == 1'b0)
    );
endmodule