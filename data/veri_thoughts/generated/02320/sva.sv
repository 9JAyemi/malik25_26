module INBUF_LVDS_MCCC_sva (
    input  logic CLK,   // External clock for checking; RTL has no clock/reset
    input  logic PADP,
    input  logic PADN,
    input  logic Y
);
    // Y equals PADP XOR PADN.
    check_xor_definition: assert property (
        @(posedge CLK) (Y == (PADP ^ PADN))
    );

    // When inputs are equal, Y is 0.
    check_equal_inputs_low_output: assert property (
        @(posedge CLK) (PADP == PADN) |=> (Y == 1'b0)
    );

    // When inputs differ, Y is 1.
    check_mismatch_inputs_high_output: assert property (
        @(posedge CLK) (PADP != PADN) |=> (Y == 1'b1)
    );

    // When PADN is 0, Y mirrors PADP.
    check_padn_zero_path: assert property (
        @(posedge CLK) (PADN == 1'b0) |=> (Y == PADP)
    );

    // When PADN is 1, Y is inverse of PADP.
    check_padn_one_path: assert property (
        @(posedge CLK) (PADN == 1'b1) |=> (Y == ~PADP)
    );

    // When PADP is 0, Y mirrors PADN.
    check_padp_zero_path: assert property (
        @(posedge CLK) (PADP == 1'b0) |=> (Y == PADN)
    );

    // When PADP is 1, Y is inverse of PADN.
    check_padp_one_path: assert property (
        @(posedge CLK) (PADP == 1'b1) |=> (Y == ~PADN)
    );
endmodule