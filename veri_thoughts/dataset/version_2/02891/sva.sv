module shift_data_sva (
    input logic CLK,
    input logic [15:0] data_in,
    input logic [3:0]  ctrl,
    input logic [15:0] data_out
);
    // No reset in DUT; pure combinational logic; assertions sample on CLK.
    // Behavior: ctrl[3:0] selects left shift by 0..14; ctrl==15 forces zero.

    // ctrl==0: pass-through.
    check_ctrl0_passthrough: assert property (
        @(posedge CLK) (ctrl == 4'd0) |-> (data_out == (data_in << 0))
    );

    // ctrl==1: shift left by 1, zero-fill.
    check_ctrl1_shift1: assert property (
        @(posedge CLK) (ctrl == 4'd1) |-> (data_out == (data_in << 1))
    );

    // ctrl==2: shift left by 2, zero-fill.
    check_ctrl2_shift2: assert property (
        @(posedge CLK) (ctrl == 4'd2) |-> (data_out == (data_in << 2))
    );

    // ctrl==3: shift left by 3, zero-fill.
    check_ctrl3_shift3: assert property (
        @(posedge CLK) (ctrl == 4'd3) |-> (data_out == (data_in << 3))
    );

    // ctrl==4: shift left by 4, zero-fill.
    check_ctrl4_shift4: assert property (
        @(posedge CLK) (ctrl == 4'd4) |-> (data_out == (data_in << 4))
    );

    // ctrl==5: shift left by 5, zero-fill.
    check_ctrl5_shift5: assert property (
        @(posedge CLK) (ctrl == 4'd5) |-> (data_out == (data_in << 5))
    );

    // ctrl==6: shift left by 6, zero-fill.
    check_ctrl6_shift6: assert property (
        @(posedge CLK) (ctrl == 4'd6) |-> (data_out == (data_in << 6))
    );

    // ctrl==7: shift left by 7, zero-fill.
    check_ctrl7_shift7: assert property (
        @(posedge CLK) (ctrl == 4'd7) |-> (data_out == (data_in << 7))
    );

    // ctrl==8: shift left by 8, zero-fill.
    check_ctrl8_shift8: assert property (
        @(posedge CLK) (ctrl == 4'd8) |-> (data_out == (data_in << 8))
    );

    // ctrl==9: shift left by 9, zero-fill.
    check_ctrl9_shift9: assert property (
        @(posedge CLK) (ctrl == 4'd9) |-> (data_out == (data_in << 9))
    );

    // ctrl==10: shift left by 10, zero-fill.
    check_ctrl10_shift10: assert property (
        @(posedge CLK) (ctrl == 4'd10) |-> (data_out == (data_in << 10))
    );

    // ctrl==11: shift left by 11, zero-fill.
    check_ctrl11_shift11: assert property (
        @(posedge CLK) (ctrl == 4'd11) |-> (data_out == (data_in << 11))
    );

    // ctrl==12: shift left by 12, zero-fill.
    check_ctrl12_shift12: assert property (
        @(posedge CLK) (ctrl == 4'd12) |-> (data_out == (data_in << 12))
    );

    // ctrl==13: shift left by 13, zero-fill.
    check_ctrl13_shift13: assert property (
        @(posedge CLK) (ctrl == 4'd13) |-> (data_out == (data_in << 13))
    );

    // ctrl==14: shift left by 14, zero-fill.
    check_ctrl14_shift14: assert property (
        @(posedge CLK) (ctrl == 4'd14) |-> (data_out == (data_in << 14))
    );

    // ctrl==15: force zero output (as coded).
    check_ctrl15_zero: assert property (
        @(posedge CLK) (ctrl == 4'd15) |-> (data_out == 16'h0000)
    );
endmodule