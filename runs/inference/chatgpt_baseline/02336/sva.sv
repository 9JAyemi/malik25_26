module MUX4_1_SL_sva (
    input logic CLK,
    input logic [1:0] Sel,
    input logic [3:0] S0,
    input logic [3:0] S1,
    input logic [3:0] S2,
    input logic [3:0] S3,
    input logic [3:0] out
);
    // Out equals S0 when Sel is 2'b00.
    check_sel00_routes_S0: assert property (
        @(posedge CLK) (Sel == 2'b00) |-> (out == S0)
    );

    // Out equals S1 when Sel is 2'b01.
    check_sel01_routes_S1: assert property (
        @(posedge CLK) (Sel == 2'b01) |-> (out == S1)
    );

    // Out equals S2 when Sel is 2'b10.
    check_sel10_routes_S2: assert property (
        @(posedge CLK) (Sel == 2'b10) |-> (out == S2)
    );

    // Out equals S3 when Sel is 2'b11.
    check_sel11_routes_S3: assert property (
        @(posedge CLK) (Sel == 2'b11) |-> (out == S3)
    );

    // Structural equivalence to the RTL ternary expression.
    check_functional_equivalence: assert property (
        @(posedge CLK) out == (Sel[1] ? (Sel[0] ? S3 : S2) : (Sel[0] ? S1 : S0))
    );

    // When Sel[1]==0, out selects between S1 and S0 per Sel[0].
    check_lower_half_select: assert property (
        @(posedge CLK) (Sel[1] == 1'b0) |-> (out == (Sel[0] ? S1 : S0))
    );

    // When Sel[1]==1, out selects between S3 and S2 per Sel[0].
    check_upper_half_select: assert property (
        @(posedge CLK) (Sel[1] == 1'b1) |-> (out == (Sel[0] ? S3 : S2))
    );

    // If all inputs are stable, output remains stable (purely combinational).
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) $stable({Sel, S0, S1, S2, S3}) |-> $stable(out)
    );
endmodule