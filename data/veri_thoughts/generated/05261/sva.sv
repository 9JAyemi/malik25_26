module main_sva (
    input logic clk,
    input logic [1:0] vc83501,
    input logic [1:0] v78d66e,
    input logic [1:0] vbb8263,
    input logic [1:0] v6f5c59
);

    // vbb8263 directly mirrors vc83501.
    check_vbb8263_matches_vc83501: assert property (
        @(posedge clk) vbb8263 == vc83501
    );

    // Bit 1 of vbb8263 matches bit 1 of vc83501.
    check_vbb8263_bit1_matches: assert property (
        @(posedge clk) vbb8263[1] == vc83501[1]
    );

    // Bit 0 of vbb8263 matches bit 0 of vc83501.
    check_vbb8263_bit0_matches: assert property (
        @(posedge clk) vbb8263[0] == vc83501[0]
    );

    // v6f5c59 is the bitwise inverse of v78d66e.
    check_v6f5c59_is_inversion_of_v78d66e: assert property (
        @(posedge clk) v6f5c59 == ~v78d66e
    );

    // Bit 1 of v6f5c59 inverts bit 1 of v78d66e.
    check_v6f5c59_bit1_inverts: assert property (
        @(posedge clk) v6f5c59[1] == ~v78d66e[1]
    );

    // Bit 0 of v6f5c59 inverts bit 0 of v78d66e.
    check_v6f5c59_bit0_inverts: assert property (
        @(posedge clk) v6f5c59[0] == ~v78d66e[0]
    );

endmodule