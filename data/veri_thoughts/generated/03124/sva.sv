module DEMUX_sva #(
    parameter n = 4
)(
    input logic clk,
    input logic in,
    input logic [n-1:0] control,
    input logic [n-1:0] out
);

    // Input low forces all outputs low.
    check_input_low_clears_out: assert property (
        @(posedge clk) (in == 1'b0) |-> (out == '0)
    );

    // control 0 selects the 1000 output pattern.
    check_control_zero_selects_1000: assert property (
        @(posedge clk) (in == 1'b1) && (control == 0) |-> (out == 4'b1000)
    );

    // control 1 selects the 0100 output pattern.
    check_control_one_selects_0100: assert property (
        @(posedge clk) (in == 1'b1) && (control == 1) |-> (out == 4'b0100)
    );

    // control 2 selects the 0010 output pattern.
    check_control_two_selects_0010: assert property (
        @(posedge clk) (in == 1'b1) && (control == 2) |-> (out == 4'b0010)
    );

    // control 3 selects the 0001 output pattern.
    check_control_three_selects_0001: assert property (
        @(posedge clk) (in == 1'b1) && (control == 3) |-> (out == 4'b0001)
    );

    // Out-of-range control drives all outputs low.
    check_invalid_control_clears_out: assert property (
        @(posedge clk) (in == 1'b1) && (control > 3) |-> (out == '0)
    );

    // Output is always either zero or one-hot.
    check_output_is_onehot0: assert property (
        @(posedge clk) $onehot0(out)
    );

    // Any asserted output requires input high.
    check_asserted_output_requires_input_high: assert property (
        @(posedge clk) (out != '0) |-> (in == 1'b1)
    );

endmodule