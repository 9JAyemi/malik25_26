module register_sva #(parameter WIDTH=8) (
    input logic clk,
    input logic reset,
    input logic xclear,
    input logic xload,
    input logic [WIDTH-1:0] xin,
    input logic [WIDTH-1:0] xout
);

    // Reset or clear forces the register output to zero on the next cycle.
    check_clear_or_reset_zero: assert property (
        @(posedge clk) disable iff (reset)
        (xclear || reset) |=> (xout == {WIDTH{1'b0}})
    );

    // Load captures xin into the register on the next cycle.
    check_load_captures_input: assert property (
        @(posedge clk) disable iff (reset)
        (!xclear && xload) |=> (xout == $past(xin))
    );

    // Without clear or load, the register holds its value.
    check_hold_when_idle: assert property (
        @(posedge clk) disable iff (reset)
        (!xclear && !xload) |=> (xout == $past(xout))
    );

endmodule