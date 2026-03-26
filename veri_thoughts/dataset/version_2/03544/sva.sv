module constmuldivmod_sva (
    input logic        clk,
    input logic [7:0]  A,
    input logic [5:0]  mode,
    input logic [7:0]  Y
);

    function automatic logic is_safe_mode(input logic [5:0] mode_i);
        is_safe_mode = (mode_i != 6'd0)  &&
                       (mode_i != 6'd1)  &&
                       (mode_i != 6'd15) &&
                       (mode_i != 6'd16) &&
                       (mode_i != 6'd30) &&
                       (mode_i != 6'd31);
    endfunction

    function automatic logic [7:0] expected_y_safe(
        input logic [7:0] A_i,
        input logic [5:0] mode_i
    );
        case (mode_i)
            6'd2:  expected_y_safe = A_i * 8'd0;
            6'd3:  expected_y_safe = A_i / 8'd1;
            6'd4:  expected_y_safe = A_i % 8'd1;
            6'd5:  expected_y_safe = A_i * 8'd1;
            6'd6:  expected_y_safe = A_i / 8'd2;
            6'd7:  expected_y_safe = A_i % 8'd2;
            6'd8:  expected_y_safe = A_i * 8'd2;
            6'd9:  expected_y_safe = A_i / 8'd4;
            6'd10: expected_y_safe = A_i % 8'd4;
            6'd11: expected_y_safe = A_i * 8'd4;
            6'd12: expected_y_safe = A_i / 8'd8;
            6'd13: expected_y_safe = A_i % 8'd8;
            6'd14: expected_y_safe = A_i * 8'd8;

            6'd17: expected_y_safe = $signed(A_i) * $signed(8'd0);
            6'd18: expected_y_safe = $signed(A_i) / $signed(8'd1);
            6'd19: expected_y_safe = $signed(A_i) % $signed(8'd1);
            6'd20: expected_y_safe = $signed(A_i) * $signed(8'd1);
            6'd21: expected_y_safe = $signed(A_i) / $signed(8'd2);
            6'd22: expected_y_safe = $signed(A_i) % $signed(8'd2);
            6'd23: expected_y_safe = $signed(A_i) * $signed(8'd2);
            6'd24: expected_y_safe = $signed(A_i) / $signed(8'd4);
            6'd25: expected_y_safe = $signed(A_i) % $signed(8'd4);
            6'd26: expected_y_safe = $signed(A_i) * $signed(8'd4);
            6'd27: expected_y_safe = $signed(A_i) / $signed(8'd8);
            6'd28: expected_y_safe = $signed(A_i) % $signed(8'd8);
            6'd29: expected_y_safe = $signed(A_i) * $signed(8'd8);

            6'd32: expected_y_safe = $signed(A_i) * $signed(-8'd0);
            6'd33: expected_y_safe = $signed(A_i) / $signed(-8'd1);
            6'd34: expected_y_safe = $signed(A_i) % $signed(-8'd1);
            6'd35: expected_y_safe = $signed(A_i) * $signed(-8'd1);
            6'd36: expected_y_safe = $signed(A_i) / $signed(-8'd2);
            6'd37: expected_y_safe = $signed(A_i) % $signed(-8'd2);
            6'd38: expected_y_safe = $signed(A_i) * $signed(-8'd2);
            6'd39: expected_y_safe = $signed(A_i) / $signed(-8'd4);
            6'd40: expected_y_safe = $signed(A_i) % $signed(-8'd4);
            6'd41: expected_y_safe = $signed(A_i) * $signed(-8'd4);
            6'd42: expected_y_safe = $signed(A_i) / $signed(-8'd8);
            6'd43: expected_y_safe = $signed(A_i) % $signed(-8'd8);
            6'd44: expected_y_safe = $signed(A_i) * $signed(-8'd8);

            default: expected_y_safe = 8'd16 * A_i;
        endcase
    endfunction

    // All modes except divide/mod-by-zero follow the RTL case table.
    check_safe_modes_match_case_table: assert property (
        @(posedge clk) is_safe_mode(mode) |-> (Y == expected_y_safe(A, mode))
    );

    // The multiply-by-zero cases always drive zero.
    check_mul_zero_modes: assert property (
        @(posedge clk) ((mode == 6'd2) || (mode == 6'd17) || (mode == 6'd32)) |-> (Y == 8'd0)
    );

    // The identity cases preserve A bit-for-bit.
    check_identity_modes: assert property (
        @(posedge clk) ((mode == 6'd3) || (mode == 6'd5) || (mode == 6'd18) || (mode == 6'd20)) |-> (Y == A)
    );

    // Unsigned and signed modulo-by-one cases produce zero.
    check_mod_one_modes: assert property (
        @(posedge clk) ((mode == 6'd4) || (mode == 6'd19)) |-> (Y == 8'd0)
    );

    // Unsigned divide-by-2/4/8 modes match the selected operation.
    check_unsigned_div_modes: assert property (
        @(posedge clk) ((mode == 6'd6) || (mode == 6'd9) || (mode == 6'd12)) |-> (Y == expected_y_safe(A, mode))
    );

    // Unsigned modulo-by-2/4/8 modes match the selected operation.
    check_unsigned_mod_modes: assert property (
        @(posedge clk) ((mode == 6'd7) || (mode == 6'd10) || (mode == 6'd13)) |-> (Y == expected_y_safe(A, mode))
    );

    // Unsigned multiply-by-2/4/8 modes match the selected operation.
    check_unsigned_mul_modes: assert property (
        @(posedge clk) ((mode == 6'd8) || (mode == 6'd11) || (mode == 6'd14)) |-> (Y == expected_y_safe(A, mode))
    );

    // Signed positive-constant modes match the selected operation.
    check_signed_positive_modes: assert property (
        @(posedge clk) ((mode >= 6'd17) && (mode <= 6'd29)) |-> (Y == expected_y_safe(A, mode))
    );

    // Signed negative-constant modes match the selected operation.
    check_signed_negative_modes: assert property (
        @(posedge clk) ((mode >= 6'd32) && (mode <= 6'd44)) |-> (Y == expected_y_safe(A, mode))
    );

    // Unlisted modes use the default multiply-by-16 behavior.
    check_default_modes: assert property (
        @(posedge clk) (mode >= 6'd45) |-> (Y == (8'd16 * A))
    );

endmodule