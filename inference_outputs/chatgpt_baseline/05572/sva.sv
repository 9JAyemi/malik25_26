module hexledx_sva (
    input logic       clk,
    input logic [3:0] value,
    input logic       blank,
    input logic       minus,
    input logic [6:0] s7
);

    // Blank forces the blanked display pattern.
    check_blank_output: assert property (
        @(posedge clk) blank |-> (s7 == ~7'b0000000)
    );

    // Minus selects the minus pattern when not blanked.
    check_minus_output: assert property (
        @(posedge clk) (!blank && minus) |-> (s7 == ~7'b1000000)
    );

    // Value 0 selects the 0 segment pattern.
    check_value_0_output: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h0)) |-> (s7 == ~7'b0111111)
    );

    // Value 1 selects the 1 segment pattern.
    check_value_1_output: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h1)) |-> (s7 == ~7'b0000110)
    );

    // Value 2 selects the 2 segment pattern.
    check_value_2_output: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h2)) |-> (s7 == ~7'b1011011)
    );

    // Value 3 selects the 3 segment pattern.
    check_value_3_output: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h3)) |-> (s7 == ~7'b1001111)
    );

    // Value 4 selects the 4 segment pattern.
    check_value_4_output: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h4)) |-> (s7 == ~7'b1100110)
    );

    // Value 5 selects the 5 segment pattern.
    check_value_5_output: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h5)) |-> (s7 == ~7'b1101101)
    );

    // Value 6 selects the 6 segment pattern.
    check_value_6_output: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h6)) |-> (s7 == ~7'b1111101)
    );

    // Value 7 selects the 7 segment pattern.
    check_value_7_output: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h7)) |-> (s7 == ~7'b0000111)
    );

    // Value 8 selects the 8 segment pattern.
    check_value_8_output: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h8)) |-> (s7 == ~7'b1111111)
    );

    // Value 9 selects the 9 segment pattern.
    check_value_9_output: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h9)) |-> (s7 == ~7'b1101111)
    );

    // Value A selects the A segment pattern.
    check_value_a_output: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hA)) |-> (s7 == ~7'b1110111)
    );

    // Value B selects the B segment pattern.
    check_value_b_output: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hB)) |-> (s7 == ~7'b1111100)
    );

    // Value C selects the C segment pattern.
    check_value_c_output: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hC)) |-> (s7 == ~7'b0111001)
    );

    // Value D selects the D segment pattern.
    check_value_d_output: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hD)) |-> (s7 == ~7'b1011110)
    );

    // Value E selects the E segment pattern.
    check_value_e_output: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hE)) |-> (s7 == ~7'b1111001)
    );

    // Value F selects the F segment pattern.
    check_value_f_output: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hF)) |-> (s7 == ~7'b1110001)
    );

endmodule