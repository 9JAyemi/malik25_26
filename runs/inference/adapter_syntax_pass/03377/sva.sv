module hex_display_sva #(
    parameter INVERT = 0
)
(
    input logic [3:0] in,
    input logic       enable,
    input logic [6:0] out
);

    function automatic logic [6:0] expected_out(input logic [3:0] v);
        begin
            case (v)
                4'h0: expected_out = 7'b0111111;
                4'h1: expected_out = 7'b0000110;
                4'h2: expected_out = 7'b1011011;
                4'h3: expected_out = 7'b1001111;
                4'h4: expected_out = 7'b1100110;
                4'h5: expected_out = 7'b1101101;
                4'h6: expected_out = 7'b1111101;
                4'h7: expected_out = 7'b0000111;
                4'h8: expected_out = 7'b1111111;
                4'h9: expected_out = 7'b1101111;
                4'ha: expected_out = 7'b1110111;
                4'hb: expected_out = 7'b1111100;
                4'hc: expected_out = 7'b0111001;
                4'hd: expected_out = 7'b1011110;
                4'he: expected_out = 7'b1111001;
                4'hf: expected_out = 7'b1110001;
                default: expected_out = 7'b0000000;
            endcase
        end
    endfunction

    // Output matches the enabled hex code or zero when disabled.
    check_output_matches_enabled_code: assert property (
        @($global_clock) out == (enable ? expected_out(in) : 7'b0000000)
    );

    // Output is always active-low when INVERT is low.
    check_output_active_low_when_not_inverted: assert property (
        @($global_clock) (INVERT == 1'b0) |-> (out == ~expected_out(in))
    );

    // Output is always active-high when INVERT is high.
    check_output_active_high_when_inverted: assert property (
        @($global_clock) (INVERT == 1'b1) |-> (out == expected_out(in))
    );

    // Enabled input 0 drives the 0 code.
    check_code_0: assert property (
        @($global_clock) (enable && (in == 4'h0)) |-> (out == 7'b0111111)
    );

    // Enabled input 1 drives the 1 code.
    check_code_1: assert property (
        @($global_clock) (enable && (in == 4'h1)) |-> (out == 7'b0000110)
    );

    // Enabled input 2 drives the 2 code.
    check_code_2: assert property (
        @($global_clock) (enable && (in == 4'h2)) |-> (out == 7'b1011011)
    );

    // Enabled input 3 drives the 3 code.
    check_code_3: assert property (
        @($global_clock) (enable && (in == 4'h3)) |-> (out == 7'b1001111)
    );

    // Enabled input 4 drives the 4 code.
    check_code_4: assert property (
        @($global_clock) (enable && (in == 4'h4)) |-> (out == 7'b1100110)
    );

    // Enabled input 5 drives the 5 code.
    check_code_5: assert property (
        @($global_clock) (enable && (in == 4'h5)) |-> (out == 7'b1101101)
    );

    // Enabled input 6 drives the 6 code.
    check_code_6: assert property (
        @($global_clock) (enable && (in == 4'h6)) |-> (out == 7'b1111101)
    );

    // Enabled input 7 drives the 7 code.
    check_code_7: assert property (
        @($global_clock) (enable && (in == 4'h7)) |-> (out == 7'b0000111)
    );

    // Enabled input 8 drives the 8 code.
    check_code_8: assert property (
        @($global_clock) (enable && (in == 4'h8)) |-> (out == 7'b1111111)
    );

    // Enabled input 9 drives the 9 code.
    check_code_9: assert property (
        @($global_clock) (enable && (in == 4'h9)) |-> (out == 7'b1101111)
    );

    // Enabled input A drives the A code.
    check_code_a: assert property (
        @($global_clock) (enable && (in == 4'ha)) |-> (out == 7'b1110111)
    );

    // Enabled input B drives the B code.
    check_code_b: assert property (
        @($global_clock) (enable && (in == 4'hb)) |-> (out == 7'b1111100)
    );

    // Enabled input C drives the C code.
    check_code_c: assert property (
        @($global_clock) (enable && (in == 4'hc)) |-> (out == 7'b0111001)
    );

    // Enabled input D drives the D code.
    check_code_d: assert property (
        @($global_clock) (enable && (in == 4'hd)) |-> (out == 7'b1011110)
    );

    // Enabled input E drives the E code.
    check_code_e: assert property (
        @($global_clock) (enable && (in == 4'he)) |-> (out == 7'b1111001)
    );

    // Enabled input F drives the F code.
    check_code_f: assert property (
        @($global_clock) (enable && (in == 4'hf)) |-> (out == 7'b1110001)
    );

endmodule