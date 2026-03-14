module addsub_sva (
    input  logic        CLK,
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic        subtract,
    input  logic [3:0]  result
);
    // In add mode, result equals A + 2*B (mod 16).
    check_add_mode_function: assert property (
        @(posedge CLK) disable iff (1'b0) (!subtract) |-> (result == ((A + B + B) & 4'hF))
    );

    // In subtract mode, result equals A + 2*(~B+1) (mod 16).
    check_sub_mode_function: assert property (
        @(posedge CLK) disable iff (1'b0) (subtract) |-> (result == ((A + (~B + 4'd1) + (~B + 4'd1)) & 4'hF))
    );

    // In subtract mode, adding 2*B back to result yields A (mod 16).
    check_sub_mode_invert_to_A: assert property (
        @(posedge CLK) disable iff (1'b0) (subtract) |-> (((result + (B << 1)) & 4'hF) == A)
    );

    // In add mode, subtracting 2*B from result yields A (mod 16).
    check_add_mode_invert_to_A: assert property (
        @(posedge CLK) disable iff (1'b0) (!subtract) |-> (((result + ((~(B << 1)) + 4'd1)) & 4'hF) == A)
    );

    // If inputs are stable, result must remain stable (pure combinational behavior).
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (1'b0) $stable({A, B, subtract}) |-> $stable(result)
    );

    // When B is zero, result passes A through regardless of subtract.
    check_B_zero_passthrough: assert property (
        @(posedge CLK) disable iff (1'b0) (B == 4'd0) |-> (result == A)
    );

    // In add mode with A=0, result equals (B << 1) (mod 16).
    check_add_mode_A_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (!subtract && (A == 4'd0)) |-> (result == ((B << 1) & 4'hF))
    );

    // In subtract mode with A=0, result equals ((~B+1) << 1) (mod 16).
    check_sub_mode_A_zero: assert property (
        @(posedge CLK) disable iff (1'b0) (subtract && (A == 4'd0)) |-> (result == (((~B + 4'd1) << 1) & 4'hF))
    );

    // When B==8, doubling cancels (mod 16) so result equals A for either mode.
    check_B_eight_passthrough: assert property (
        @(posedge CLK) disable iff (1'b0) (B == 4'h8) |-> (result == A)
    );

    // In subtract mode with B==15, result equals A + 2 (mod 16).
    check_sub_mode_B_15: assert property (
        @(posedge CLK) disable iff (1'b0) (subtract && (B == 4'hF)) |-> (result == ((A + 4'd2) & 4'hF))
    );
endmodule