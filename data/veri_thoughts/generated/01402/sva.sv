module logic_function_sva (
    input logic clk,
    input logic rst,
    input logic [3:0] din,
    input logic dout
);
    // Clock: clk (posedge). Reset: rst active-high.
    // Logic: combinational; dout = ~(^din).

    // dout equals the inversion of the XOR-reduction of din.
    check_inverted_parity_function: assert property (
        @(posedge clk) disable iff (rst) (dout === ~(^din))
    );

    // When din has even parity, dout must be 1.
    check_even_parity_high: assert property (
        @(posedge clk) disable iff (rst) ((^din) === 1'b0) |-> (dout === 1'b1)
    );

    // When din has odd parity, dout must be 0.
    check_odd_parity_low: assert property (
        @(posedge clk) disable iff (rst) ((^din) === 1'b1) |-> (dout === 1'b0)
    );

    // Specific case: all zeros input yields dout=1 (even parity).
    check_all_zeros_high: assert property (
        @(posedge clk) disable iff (rst) (din == 4'b0000) |-> (dout === 1'b1)
    );

    // Specific case: all ones input yields dout=1 (even parity).
    check_all_ones_high: assert property (
        @(posedge clk) disable iff (rst) (din == 4'b1111) |-> (dout === 1'b1)
    );
endmodule