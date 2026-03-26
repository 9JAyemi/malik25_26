module multiplexer_sva #(parameter N = 1) (
    input logic clk,
    input logic ctrl,
    input logic [N-1:0] D0,
    input logic [N-1:0] D1,
    input logic [N-1:0] S
);

    // Sampling clock only; the RTL has no clock or reset.
    // The DUT is a combinational N-bit 2:1 mux controlled by ctrl.

    // S matches the implemented mux expression on every sample.
    check_mux_function: assert property (
        @(posedge clk) disable iff (1'b0)
        S === ((ctrl == 1'b0) ? D0 : D1)
    );

    // When ctrl is low, S selects D0.
    check_select_d0: assert property (
        @(posedge clk) disable iff (1'b0)
        (ctrl === 1'b0) |-> (S === D0)
    );

    // When ctrl is high, S selects D1.
    check_select_d1: assert property (
        @(posedge clk) disable iff (1'b0)
        (ctrl === 1'b1) |-> (S === D1)
    );

    // If ctrl stays low and D0 is stable, S stays stable.
    check_stable_when_d0_selected: assert property (
        @(posedge clk) disable iff (1'b0)
        (ctrl === 1'b0) && $stable(ctrl) && $stable(D0) |-> $stable(S)
    );

    // If ctrl stays high and D1 is stable, S stays stable.
    check_stable_when_d1_selected: assert property (
        @(posedge clk) disable iff (1'b0)
        (ctrl === 1'b1) && $stable(ctrl) && $stable(D1) |-> $stable(S)
    );

endmodule