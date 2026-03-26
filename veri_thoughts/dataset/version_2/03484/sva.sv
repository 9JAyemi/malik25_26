module bitwise_and_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] out
);

    // RTL has no clock or reset; clk is an external sampling clock.

    // Upper output bits are the bitwise AND of the corresponding input bits.
    check_upper_bits_and: assert property (
        @(posedge clk) out[7:1] == (a[7:1] & b[7:1])
    );

    // Unchanged upper input bits keep the upper output bits unchanged.
    check_upper_bits_stable_when_inputs_stable: assert property (
        @(posedge clk)
        !$initstate &&
        (a[7:1] == $past(a[7:1])) &&
        (b[7:1] == $past(b[7:1]))
        |-> (out[7:1] == $past(out[7:1]))
    );

    // The LSB is only assigned in the initial block and then remains constant.
    check_lsb_constant_after_initialization: assert property (
        @(posedge clk) 1'b1 |=> $stable(out[0])
    );

endmodule