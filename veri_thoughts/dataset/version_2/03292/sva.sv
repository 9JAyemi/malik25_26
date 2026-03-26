module toggle_module_sva #(
    parameter WIDTH = 1
)(
    input logic clk,
    input logic toggle,
    input logic [WIDTH-1:0] out
);

    // When toggle is low, out holds its previous value.
    check_hold_when_no_toggle: assert property (
        @(posedge clk) !toggle |=> $stable(out)
    );

    // A toggle from zero drives out to 1 on the next cycle.
    check_toggle_from_zero_sets_one: assert property (
        @(posedge clk) (toggle && !out) |=> (out == {{(WIDTH-1){1'b0}}, 1'b1})
    );

    // A toggle from any non-zero value drives out to 0 on the next cycle.
    check_toggle_from_nonzero_clears_out: assert property (
        @(posedge clk) (toggle && out) |=> (out == '0)
    );

endmodule