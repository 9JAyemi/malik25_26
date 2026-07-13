module fix_shifter_sva (
    input logic clk,
    input logic [31:0] dout,
    input logic [31:0] B,
    input logic [1:0]  ctrl,
    input logic [1:0]  A
);
    // dout matches the RTL ternary shift selection for all ctrl values.
    check_dout_matches_muxed_shift: assert property (
        @(posedge clk) dout == ((ctrl == 2'b00) ? (B << A) :
                                (ctrl == 2'b01) ? (B << (A + 1)) :
                                (ctrl == 2'b10) ? (B << (A + 2)) :
                                                  (B << (A + 3)))
    );

    // When ctrl==00, dout equals B shifted left by A.
    check_ctrl00_shift: assert property (
        @(posedge clk) (ctrl == 2'b00) |-> (dout == (B << A))
    );

    // When ctrl==01, dout equals B shifted left by A+1.
    check_ctrl01_shift: assert property (
        @(posedge clk) (ctrl == 2'b01) |-> (dout == (B << (A + 1)))
    );

    // When ctrl==10, dout equals B shifted left by A+2.
    check_ctrl10_shift: assert property (
        @(posedge clk) (ctrl == 2'b10) |-> (dout == (B << (A + 2)))
    );

    // When ctrl==11, dout equals B shifted left by A+3.
    check_ctrl11_shift: assert property (
        @(posedge clk) (ctrl == 2'b11) |-> (dout == (B << (A + 3)))
    );

    // If inputs A,B,ctrl are stable, dout must remain stable.
    check_stable_on_stable_inputs: assert property (
        @(posedge clk) $stable({A, B, ctrl}) |-> $stable(dout)
    );

    // No-shift case: when A==0 and ctrl==0, dout equals B.
    check_no_shift_when_ctrl00_A00: assert property (
        @(posedge clk) ((A == 2'b00) && (ctrl == 2'b00)) |-> (dout == B)
    );

    // Compact equivalence: dout equals B shifted by (A + ctrl).
    check_equiv_compact_shift_amount: assert property (
        @(posedge clk) dout == (B << (A + ctrl))
    );

    // Zero input propagates: if B is zero, dout must be zero.
    check_zero_input_zero_output: assert property (
        @(posedge clk) (B == 32'b0) |-> (dout == 32'b0)
    );

    // Max shift example: when A==3 and ctrl==3, dout equals B << 6.
    check_max_shift_case: assert property (
        @(posedge clk) ((A == 2'b11) && (ctrl == 2'b11)) |-> (dout == (B << 6))
    );
endmodule