module hexledx_sva (
    input logic       clk,
    input logic [3:0] value,
    input logic       blank,
    input logic       minus,
    input logic [6:0] s7
);

// blank forces the output high.
    check_blank_forces_high: assert property (
        @(posedge clk) blank |-> (s7 == 7'b1111111)
    );

// minus selects the dash pattern when blank is low.
    check_minus_selects_dash: assert property (
        @(posedge clk) (!blank && minus) |-> (s7 == 7'b1000000)
    );

// value 0 selects the 0 pattern when blank and minus are low.
    check_value_0_selects_0: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h0)) |-> (s7 == 7'b0111111)
    );

// value 1 selects the 1 pattern when blank and minus are low.
    check_value_1_selects_1: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h1)) |-> (s7 == 7'b0000110)
    );

// value 2 selects the 2 pattern when blank and minus are low.
    check_value_2_selects_2: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h2)) |-> (s7 == 7'b1011011)
    );

// value 3 selects the 3 pattern when blank and minus are low.
    check_value_3_selects_3: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h3)) |-> (s7 == 7'b1001111)
    );

// value 4 selects the 4 pattern when blank and minus are low.
    check_value_4_selects_4: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h4)) |-> (s7 == 7'b1100110)
    );

// value 5 selects the 5 pattern when blank and minus are low.
    check_value_5_selects_5: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h5)) |-> (s7 == 7'b1101101)
    );

// value 6 selects the 6 pattern when blank and minus are low.
    check_value_6_selects_6: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h6)) |-> (s7 == 7'b1111101)
    );

// value 7 selects the 7 pattern when blank and minus are low.
    check_value_7_selects_7: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h7)) |-> (s7 == 7'b0000111)
    );

// value 8 selects the 8 pattern when blank and minus are low.
    check_value_8_selects_8: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h8)) |-> (s7 == 7'b1111111)
    );

// value 9 selects the 9 pattern when blank and minus are low.
    check_value_9_selects_9: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'h9)) |-> (s7 == 7'b1101111)
    );

// value A selects the A pattern when blank and minus are low.
    check_value_a_selects_a: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hA)) |-> (s7 == 7'b1110111)
    );

// value B selects the B pattern when blank and minus are low.
    check_value_b_selects_b: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hB)) |-> (s7 == 7'b1111100)
    );

// value C selects the C pattern when blank and minus are low.
    check_value_c_selects_c: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hC)) |-> (s7 == 7'b0111001)
    );

// value D selects the D pattern when blank and minus are low.
    check_value_d_selects_d: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hD)) |-> (s7 == 7'b1011110)
    );

// value E selects the E pattern when blank and minus are low.
    check_value_e_selects_e: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hE)) |-> (s7 == 7'b1111001)
    );

// value F selects the F pattern when blank and minus are low.
    check_value_f_selects_f: assert property (
        @(posedge clk) (!blank && !minus && (value == 4'hF)) |-> (s7 == 7'b1110001)
    );

endmodule
