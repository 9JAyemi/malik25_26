module sky130_fd_sc_ls__clkinv_sva (
    input logic clk,
    input logic Y,
    input logic A
);

    // Y must always be the inversion of A.
    check_inverter_function: assert property (
        @(posedge clk) Y === ~A
    );

    // A rising at the sample point must drive Y low.
    check_a_rise_drives_y_low: assert property (
        @(posedge clk) $rose(A) |-> (Y === 1'b0)
    );

    // A falling at the sample point must drive Y high.
    check_a_fall_drives_y_high: assert property (
        @(posedge clk) $fell(A) |-> (Y === 1'b1)
    );

    // If A is unchanged between samples, Y must also be unchanged.
    check_stable_input_keeps_stable_output: assert property (
        @(posedge clk) $stable(A) |-> $stable(Y)
    );

endmodule