module RingCounter_sva #(
    parameter int n = 4
)(
    input logic clk,
    input logic [n-1:0] out
);

    // Out advances by one modulo 2^n on each clock.
    check_out_modulo_increment: assert property (
        @(posedge clk) 1'b1 |=> (out == ($past(out) + 1'b1))
    );

    // Out wraps to zero after reaching the maximum value.
    check_out_wraps_to_zero: assert property (
        @(posedge clk) (out == {n{1'b1}}) |=> (out == {n{1'b0}})
    );

    // Out increments normally when it is not at the maximum value.
    check_out_increments_before_wrap: assert property (
        @(posedge clk) (out != {n{1'b1}}) |=> (out == ($past(out) + 1'b1))
    );

    // Out changes on every clock edge.
    check_out_changes_every_cycle: assert property (
        @(posedge clk) 1'b1 |=> (out != $past(out))
    );

endmodule