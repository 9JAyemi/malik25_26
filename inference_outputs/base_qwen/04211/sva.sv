```systemverilog
module barrel_shifter_sva (
    input logic clk,
    input logic rst_n,
    input logic [15:0] in,
    input logic [3:0] shift_amt,
    input logic shift_left,
    output logic [15:0] out
);
    // Shift left operation
    shift_left_check: assert property (
        @(posedge clk) disable iff (!rst_n) (shift_left == 1'b1) |-> (out == (in << shift_amt))
    );
    // Shift right operation
    shift_right_check: assert property (
        @(posedge clk) disable iff (!rst_n) (shift_left == 1'b0) |-> (out == (in >> shift_amt))
    );
    // Output is zero when shift amount is zero
    zero_shift_check: assert property (
        @(posedge clk) disable iff (!rst_n) (shift_amt == 4'b0000) |-> (out == 16'b0)
    );
    // Output is the same as input when shift amount is maximum
    max_shift_check: assert property (
        @(posedge clk) disable iff (!rst_n) (shift_amt == 4'b1111) |-> (shift_left ? (out == (in << 15)) : (out == (in >> 1)))
    );
    // Output is zero when reset is active
    reset_check: assert property (
        @(posedge clk) !rst_n |-> (out == 16'b0)
    );
endmodule
```