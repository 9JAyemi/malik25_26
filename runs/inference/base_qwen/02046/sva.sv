module and4_pwr_good_sva (
    input logic A_N,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    output logic X,
    output logic pwrgood_pp0_out_X
);
    // No clock or reset signals are present in the RTL

    // Combinational logic: Invert A_N input
    invert_A_N: assert property (
        @(posedge VPB) disable iff (!VPB) A_N |-> (not0_out == ~A_N)
    );

    // Combinational logic: Perform AND operation on inputs B, C, and D
    and_operation: assert property (
        @(posedge VPB) disable iff (!VPB) (B & C & D) |-> (and0_out_X == (not0_out & B & C & D))
    );

    // Combinational logic: Create power good output
    power_good_output: assert property (
        @(posedge VPB) disable iff (!VPB) (and0_out_X & VPWR & VGND) |-> (pwrgood_pp0_out_X == (and0_out_X & VPWR & VGND))
    );

    // Combinational logic: Buffer output to X
    buffer_output: assert property (
        @(posedge VPB) disable iff (!VPB) (pwrgood_pp0_out_X) |-> (X == pwrgood_pp0_out_X)
    );
endmodule