module mux4to1_using_full_adders_assertions (
    input logic       clk,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic [3:0] out
);

    // Out is the carry result of the third full-adder stage.
    check_out_matches_stage3_carry: assert property (
        @(posedge clk)
        out == (
            ((in0 ^ in1 ^ {4{sel[0]}}) & (in2 ^ in3 ^ {4{sel[0]}})) |
            ({4{sel[1]}} & ((in0 ^ in1 ^ {4{sel[0]}}) ^ (in2 ^ in3 ^ {4{sel[0]}})))
        )
    );

    // With sel[1] low, out is the AND of the first two stage sums.
    check_sel1_low_uses_and_of_stage_sums: assert property (
        @(posedge clk)
        (sel[1] == 1'b0) |-> (
            out == ((in0 ^ in1 ^ {4{sel[0]}}) & (in2 ^ in3 ^ {4{sel[0]}}))
        )
    );

    // With sel[1] high, out is the OR of the first two stage sums.
    check_sel1_high_uses_or_of_stage_sums: assert property (
        @(posedge clk)
        (sel[1] == 1'b1) |-> (
            out == ((in0 ^ in1 ^ {4{sel[0]}}) | (in2 ^ in3 ^ {4{sel[0]}}))
        )
    );

    // sel=00 produces the AND of the pairwise XOR terms.
    check_sel00_and_of_xors: assert property (
        @(posedge clk)
        (sel == 2'b00) |-> (out == ((in0 ^ in1) & (in2 ^ in3)))
    );

    // sel=01 produces the AND of the pairwise XNOR terms.
    check_sel01_and_of_xnors: assert property (
        @(posedge clk)
        (sel == 2'b01) |-> (out == ((in0 ~^ in1) & (in2 ~^ in3)))
    );

    // sel=10 produces the OR of the pairwise XOR terms.
    check_sel10_or_of_xors: assert property (
        @(posedge clk)
        (sel == 2'b10) |-> (out == ((in0 ^ in1) | (in2 ^ in3)))
    );

    // sel=11 produces the OR of the pairwise XNOR terms.
    check_sel11_or_of_xnors: assert property (
        @(posedge clk)
        (sel == 2'b11) |-> (out == ((in0 ~^ in1) | (in2 ~^ in3)))
    );

endmodule