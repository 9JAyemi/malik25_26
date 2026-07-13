module sky130_fd_sc_ms__einvp_sva (
    input logic clk, // external verification clock
    input logic Z,   // DUT output
    input logic A,   // DUT input
    input logic TE   // DUT input (enable, active-high)
);
    // No reset in DUT; assertions are always active (disable iff (1'b0)).
    // DUT is combinational tri-state inverter: TE=1 => Z=~A; TE=0 => Z='z.

    // When enabled, Z equals bitwise inversion of A.
    check_inversion_when_enabled: assert property (
        @(posedge clk) disable iff (1'b0) (TE === 1'b1) |-> (Z === ~A)
    );

    // When disabled, Z is high-impedance.
    check_highz_when_disabled: assert property (
        @(posedge clk) disable iff (1'b0) (TE === 1'b0) |-> (Z === 1'bz)
    );

    // When enabled, Z is never high-impedance.
    check_not_z_when_enabled: assert property (
        @(posedge clk) disable iff (1'b0) (TE === 1'b1) |-> (Z !== 1'bz)
    );

    // When enabled and A=0, Z must be 1.
    check_drive_one_when_A0: assert property (
        @(posedge clk) disable iff (1'b0) (TE === 1'b1 && A === 1'b0) |-> (Z === 1'b1)
    );

    // When enabled and A=1, Z must be 0.
    check_drive_zero_when_A1: assert property (
        @(posedge clk) disable iff (1'b0) (TE === 1'b1 && A === 1'b1) |-> (Z === 1'b0)
    );

    // If enabled across cycles and A is stable, Z remains stable.
    check_stability_when_enabled_and_A_stable: assert property (
        @(posedge clk) disable iff (1'b0) (TE === 1'b1 && $past(TE) === 1'b1 && (A === $past(A))) |-> (Z === $past(Z))
    );
endmodule