module sync_reset_dff_assertions (
    input logic clk,
    input logic rst,
    input logic d,
    input logic q
);

    // q must be low whenever reset is asserted.
    check_reset_clears_q: assert property (
        @(posedge clk) !rst |-> (q == 1'b0)
    );

    // q stays at the reset value on the first clock where reset is released.
    check_reset_release_holds_zero_on_sampled_edge: assert property (
        @(posedge clk) $rose(rst) |-> (q == 1'b0)
    );

    // A high d must be captured into q on the next active clock.
    check_capture_one: assert property (
        @(posedge clk) disable iff (!rst) d |=> (q == 1'b1)
    );

    // A low d must be captured into q on the next active clock.
    check_capture_zero: assert property (
        @(posedge clk) disable iff (!rst) !d |=> (q == 1'b0)
    );

endmodule