module hexledx_sva (
    input logic       clk,
    input logic [3:0] value,
    input logic       blank,
    input logic       minus,
    input logic [6:0] s7
);

    // blank forces all segments on.
    check_blank_forces_all_segments: assert property (
        @(posedge clk) blank |-> (s7 == ~7'b0000000)
    );

    // minus forces only the decimal point on.
    check_minus_forces_decimal_point: assert property (
        @(posedge clk) (!blank && minus) |-> (s7 == ~7'b1000000)
    );

    // value 0 maps to 0111111.
    check_value_0_mapping: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h0)) |-> (s7 == ~7'b0111111)
    );

    // value 1 maps to 0000110.
    check_value_1_mapping: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h1)) |-> (s7 == ~7'b0000110)
    );

    // value 2 maps to 1011011.
    check_value_2_mapping: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h2)) |-> (s7 == ~7'b1011011)
    );

    // value 3 maps to 1001111.
    check_value_3_mapping: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h3)) |-> (s7 == ~7'b1001111)
    );

    // value 4 maps to 1100110.
    check_value_4_mapping: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h4)) |-> (s7 == ~7'b1100110)
    );

    // value 5 maps to 1101101.
    check_value_5_mapping: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h5)) |-> (s7 == ~7'b1101101)
    );

    // value 6 maps to 1111101.
    check_value_6_mapping: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h6)) |-> (s7 == ~7'b1111101)
    );

    // value 7 maps to 0000111.
    check_value_7_mapping: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h7)) |-> (s7 == ~7'b0000111)
    );

    // value 8 maps to 1111111.
    check_value_8_mapping: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h8)) |-> (s7 == ~7'b1111111)
    );

    // value 9 maps to 1101111.
    check_value_9_mapping: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h9)) |-> (s7 == ~7'b1101111)
    );

    // value A maps to 1110111.
    check_value_a_mapping: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hA)) |-> (s7 == ~7'b1110111)
    );

    // value B maps to 1111100.
    check_value_b_mapping: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hB)) |-> (s7 == ~7'b1111100)
    );

    // value C maps to 0111001.
    check_value_c_mapping: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hC)) |-> (s7 == ~7'b0111001)
    );

    // value D maps to 1011110.
    check_value_d_mapping: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hD)) |-> (s7 == ~7'b1011110)
    );

    // value E maps to 1111001.
    check_value_e_mapping: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hE)) |-> (s7 == ~7'b1111001)
    );

    // value F maps to 1110001.
    check_value_f_mapping: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hF)) |-> (s7 == ~7'b1110001)
    );

endmodule