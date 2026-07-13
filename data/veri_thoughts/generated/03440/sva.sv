module barrel_shifter_sva (
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0] SHIFT,
    input logic clk,
    input logic [15:0] S
);

    // S must register the selected shift result from the previous cycle.
    check_registered_shift_function: assert property (
        @(posedge clk) disable iff ($initstate)
        S == ($past(SHIFT[3]) ? ($past(B) >> 4'd8) : ($past(A) << $past(SHIFT)))
    );

    // Low SHIFT values must select the A left-shift path.
    check_a_path_when_shift_msb_low: assert property (
        @(posedge clk) disable iff ($initstate)
        !$past(SHIFT[3]) |-> (S == ($past(A) << $past(SHIFT)))
    );

    // High SHIFT values must select the B right-shift-by-8 path.
    check_b_path_when_shift_msb_high: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(SHIFT[3]) |-> (S == ($past(B) >> 4'd8))
    );

    // SHIFT value 0 must pass A through to the registered output.
    check_shift_zero_passthrough: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(SHIFT) == 4'h0) |-> (S == $past(A))
    );

    // SHIFT value 7 must left shift A by seven bits.
    check_shift_seven_left: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(SHIFT) == 4'h7) |-> (S == ($past(A) << 4'd7))
    );

    // SHIFT value 8 must use B shifted right by eight bits.
    check_shift_eight_uses_b: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(SHIFT) == 4'h8) |-> (S == ($past(B) >> 4'd8))
    );

    // SHIFT value 15 must also use B shifted right by eight bits.
    check_shift_fifteen_uses_b: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(SHIFT) == 4'hF) |-> (S == ($past(B) >> 4'd8))
    );

    // The upper byte must clear when the B path is selected.
    check_b_path_upper_byte_zero: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(SHIFT[3]) |-> (S[15:8] == 8'h00)
    );

    // The lower byte must match B[15:8] when the B path is selected.
    check_b_path_lower_byte_matches_b_upper: assert property (
        @(posedge clk) disable iff ($initstate)
        $past(SHIFT[3]) |-> (S[7:0] == $past(B[15:8]))
    );

endmodule