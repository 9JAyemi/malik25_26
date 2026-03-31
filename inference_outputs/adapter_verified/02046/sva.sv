module and4_pwr_good_sva (
    input logic clk,
    input logic X,
    input logic pwrgood_pp0_out_X,
    input logic A_N,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

// pwrgood_pp0_out_X must equal X.
    check_pwrgood_equals_x: assert property (
        @(posedge clk) pwrgood_pp0_out_X == X
    );

// X must equal pwrgood_pp0_out_X.
    check_x_equals_pwrgood: assert property (
        @(posedge clk) X == pwrgood_pp0_out_X
    );

// X must equal the AND of not(A_N), B, C, D, VPWR, and VGND.
    check_x_function: assert property (
        @(posedge clk) X == (~A_N & B & C & D & VPWR & VGND)
    );

// A_N high forces X low.
    check_a_n_high_forces_x_low: assert property (
        @(posedge clk) A_N |-> !X
    );

// B low forces X low.
    check_b_low_forces_x_low: assert property (
        @(posedge clk) !B |-> !X
    );

// C low forces X low.
    check_c_low_forces_x_low: assert property (
        @(posedge clk) !C |-> !X
    );

// D low forces X low.
    check_d_low_forces_x_low: assert property (
        @(posedge clk) !D |-> !X
    );

// VPWR low forces X low.
    check_vpwr_low_forces_x_low: assert property (
        @(posedge clk) !VPWR |-> !X
    );

// VGND low forces X low.
    check_vgnd_low_forces_x_low: assert property (
        @(posedge clk) !VGND |-> !X
    );

// All required inputs high drive X high.
    check_all_inputs_high_drive_x_high: assert property (
        @(posedge clk) (!A_N && B && C && D && VPWR && VGND) |-> X
    );

endmodule
