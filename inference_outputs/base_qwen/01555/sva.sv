```systemverilog
module barrel_shifter_sva (
    input logic clk,
    input logic rst_n,
    input logic [15:0] in,
    input logic [3:0] shift,
    input logic dir,
    output logic [15:0] out
);
    // Shift direction must be either 0 (left) or 1 (right)
    direction_check: assert property (
        @(posedge clk) disable iff (!rst_n) (dir == 0 || dir == 1)
    );

    // Shift amount must be within the valid range [0, 15]
    shift_amount_check: assert property (
        @(posedge clk) disable iff (!rst_n) (shift >= 4'b0000 && shift <= 4'b1111)
    );

    // Output should be the result of the shift operation
    shift_result_check: assert property (
        @(posedge clk) disable iff (!rst_n) (out == (dir == 0) ? (in << shift) : (in >> shift))
    );

    // Output should be zero when shift amount is zero
    zero_shift_check: assert property (
        @(posedge clk) disable iff (!rst_n) (shift == 4'b0000 |-> out == 16'b0000000000000000)
    );

    // Output should be the same as input when shift amount is maximum
    max_shift_check: assert property (
        @(posedge clk) disable iff (!rst_n) (shift == 4'b1111 |-> out == (dir == 0) ? (in << 15) : (in >> 1))
    );

    // Output should be zero when reset is active
    reset_check: assert property (
        @(posedge clk) !rst_n |-> out == 16'b0000000000000000
    );
endmodule
```