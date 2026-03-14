module shifter_sva (
    input logic CLK,
    input logic [31:0] dout,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [1:0] ctrl
);
    // ctrl=00: dout equals B left-shifted by A[4:0].
    check_left_shift_correctness: assert property (
        @(posedge CLK) (ctrl == 2'b00) |-> (dout == (B << A[4:0]))
    );

    // ctrl=01: dout equals B logical-right-shifted by A[4:0].
    check_right_logical_shift_correctness: assert property (
        @(posedge CLK) (ctrl == 2'b01) |-> (dout == (B >> A[4:0]))
    );

    // ctrl=11: dout equals B arithmetic-right-shifted by A[4:0].
    check_right_arith_shift_correctness: assert property (
        @(posedge CLK) (ctrl == 2'b11) |-> (dout == ($signed(B) >>> A[4:0]))
    );

    // ctrl=10 (default): dout passes B unchanged.
    check_noop_ctrl_10_outputs_input: assert property (
        @(posedge CLK) (ctrl == 2'b10) |-> (dout == B)
    );

    // Zero shift amount yields passthrough regardless of ctrl.
    check_zero_shift_amount_no_change: assert property (
        @(posedge CLK) (A[4:0] == 5'd0) |-> (dout == B)
    );

    // Left shift with nonzero amount forces LSB to 0.
    check_left_shift_lsb_zero: assert property (
        @(posedge CLK) (ctrl == 2'b00 && (A[4:0] != 5'd0)) |-> (dout[0] == 1'b0)
    );

    // Logical right shift with nonzero amount forces MSB to 0.
    check_logical_right_msb_zero: assert property (
        @(posedge CLK) (ctrl == 2'b01 && (A[4:0] != 5'd0)) |-> (dout[31] == 1'b0)
    );

    // Arithmetic right shift with nonzero amount preserves sign bit.
    check_arith_right_sign_preserved: assert property (
        @(posedge CLK) (ctrl == 2'b11 && (A[4:0] != 5'd0)) |-> (dout[31] == B[31])
    );

    // Zero data input always yields zero output.
    check_zero_data_maps_to_zero: assert property (
        @(posedge CLK) (B == 32'h0) |-> (dout == 32'h0)
    );

    // Full functional spec matches ctrl selection and A[4:0] shift amount.
    check_full_functional_spec: assert property (
        @(posedge CLK)
            dout == ((ctrl == 2'b00) ? (B << A[4:0]) :
                     (ctrl == 2'b01) ? (B >> A[4:0]) :
                     (ctrl == 2'b11) ? ($signed(B) >>> A[4:0]) :
                                       B)
    );
endmodule