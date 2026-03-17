module adder_subtractor_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic sub,
    input logic clk,
    input logic rst,
    input logic [3:0] out,
    input logic cout
);

    // Clock: clk. Reset: rst, active-high synchronous.
    // Mixed logic: combinational operand preprocessing with sequential outputs.

    // Synchronous reset clears the registered output and carry on the next cycle.
    check_reset_clears_outputs: assert property (
        @(posedge clk) (rst == 1'b1) |=> ({cout, out} == 5'h00)
    );

    // In add mode, the next output is A + B + current cout, with the carry bit truncated.
    check_add_mode_update: assert property (
        @(posedge clk) disable iff (rst)
        (sub == 1'b0) |=> ({cout, out} == {1'b0, ($past(A) + $past(B) + $past(cout))})
    );

    // In subtract mode, the next output uses ~A and two's-complement B, with the carry bit truncated.
    check_sub_mode_update: assert property (
        @(posedge clk) disable iff (rst)
        (sub == 1'b1) |=> ({cout, out} == {1'b0, ((~$past(A)) + ((~$past(B)) + 4'h1) + $past(cout))})
    );

    // Every non-reset update drives the registered carry output low.
    check_carry_zero_after_update: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (cout == 1'b0)
    );

endmodule