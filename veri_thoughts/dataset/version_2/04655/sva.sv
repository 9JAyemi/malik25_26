module karnaugh_map_5_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic F
);

    // AB=00 drives F with the parity of C, D, and E.
    check_ab00_parity: assert property (
        @(posedge clk)
        (!$isunknown({A,B,C,D,E}) && (A == 1'b0) && (B == 1'b0)) |-> (F === (C ^ D ^ E))
    );

    // AB=01 drives F with the inverted parity of C, D, and E.
    check_ab01_inverted_parity: assert property (
        @(posedge clk)
        (!$isunknown({A,B,C,D,E}) && (A == 1'b0) && (B == 1'b1)) |-> (F === ~(C ^ D ^ E))
    );

    // AB=10 drives F with the parity of C, D, and E.
    check_ab10_parity: assert property (
        @(posedge clk)
        (!$isunknown({A,B,C,D,E}) && (A == 1'b1) && (B == 1'b0)) |-> (F === (C ^ D ^ E))
    );

    // AB=11 drives F with the inverted parity of C, D, and E.
    check_ab11_inverted_parity: assert property (
        @(posedge clk)
        (!$isunknown({A,B,C,D,E}) && (A == 1'b1) && (B == 1'b1)) |-> (F === ~(C ^ D ^ E))
    );

    // Overall, F reduces to B xor C xor D xor E.
    check_overall_xor_function: assert property (
        @(posedge clk)
        !$isunknown({A,B,C,D,E}) |-> (F === (B ^ C ^ D ^ E))
    );

endmodule