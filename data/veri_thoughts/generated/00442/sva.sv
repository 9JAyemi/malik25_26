module tap_point_sva(
    input logic clk,
    input logic vin,
    input logic gnd,
    input logic tap
);

    // Tap must match the RTL combinational expression.
    check_tap_equation: assert property (
        @(posedge clk)
        tap === ((vin - gnd) ? vin : gnd)
    );

    // When vin and gnd are equal binary values, tap selects gnd.
    check_equal_inputs_select_gnd: assert property (
        @(posedge clk)
        (((vin === 1'b0) && (gnd === 1'b0)) || ((vin === 1'b1) && (gnd === 1'b1)))
        |-> (tap === gnd)
    );

    // When vin and gnd differ as binary values, tap selects vin.
    check_different_inputs_select_vin: assert property (
        @(posedge clk)
        (((vin === 1'b0) && (gnd === 1'b1)) || ((vin === 1'b1) && (gnd === 1'b0)))
        |-> (tap === vin)
    );

endmodule