module Span12Mux_h9_sva (
    input logic CLK,      // external clock for SVA only
    input logic [11:0] I,
    input logic [3:0]  S,
    input logic        O
);

    // S=0 selects I[0]
    check_s0_selects_i0: assert property (
        @(posedge CLK) (S == 4'd0) |-> (O == I[0])
    );

    // S=1 selects I[1]
    check_s1_selects_i1: assert property (
        @(posedge CLK) (S == 4'd1) |-> (O == I[1])
    );

    // S=2 selects I[2]
    check_s2_selects_i2: assert property (
        @(posedge CLK) (S == 4'd2) |-> (O == I[2])
    );

    // S=3 selects I[3]
    check_s3_selects_i3: assert property (
        @(posedge CLK) (S == 4'd3) |-> (O == I[3])
    );

    // S=4 selects I[4]
    check_s4_selects_i4: assert property (
        @(posedge CLK) (S == 4'd4) |-> (O == I[4])
    );

    // S=5 selects I[5]
    check_s5_selects_i5: assert property (
        @(posedge CLK) (S == 4'd5) |-> (O == I[5])
    );

    // S=6 selects I[6]
    check_s6_selects_i6: assert property (
        @(posedge CLK) (S == 4'd6) |-> (O == I[6])
    );

    // S=7 selects I[7]
    check_s7_selects_i7: assert property (
        @(posedge CLK) (S == 4'd7) |-> (O == I[7])
    );

    // S=8 selects I[8]
    check_s8_selects_i8: assert property (
        @(posedge CLK) (S == 4'd8) |-> (O == I[8])
    );

    // S=9 selects I[9]
    check_s9_selects_i9: assert property (
        @(posedge CLK) (S == 4'd9) |-> (O == I[9])
    );

    // S=10 selects I[10]
    check_s10_selects_i10: assert property (
        @(posedge CLK) (S == 4'd10) |-> (O == I[10])
    );

    // S=11 selects I[11]
    check_s11_selects_i11: assert property (
        @(posedge CLK) (S == 4'd11) |-> (O == I[11])
    );

    // S out of range (12..15) drives O=0
    check_default_zero_when_s_ge_12: assert property (
        @(posedge CLK) (S >= 4'd12) |-> (O == 1'b0)
    );

    // If S and I are stable across a cycle, O remains stable
    check_output_stable_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(S) && $stable(I)) |-> $stable(O)
    );

endmodule