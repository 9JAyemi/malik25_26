module f1_TECH_AND18_sva (
    input logic [17:0] in,
    input logic        out
);
    // out matches the reduction AND of all input bits.
    check_out_matches_reduction_and: assert property (
        @($global_clock) out == (&in)
    );
endmodule

module f1_TECH_AND4_sva (
    input logic [3:0] in,
    input logic       out
);
    // out matches the reduction AND of all input bits.
    check_out_matches_reduction_and: assert property (
        @($global_clock) out == (&in)
    );
endmodule

module f2_TECH_AND5_sva (
    input logic [4:0] in,
    input logic       out
);
    // out matches the reduction AND of all input bits.
    check_out_matches_reduction_and: assert property (
        @($global_clock) out == (&in)
    );
endmodule

module f3_TECH_NAND18_sva (
    input logic [17:0] in,
    input logic        out
);
    // out matches the reduction NAND of all input bits.
    check_out_matches_reduction_nand: assert property (
        @($global_clock) out == (~(&in))
    );
endmodule

module f3_TECH_NAND4_sva (
    input logic [3:0] in,
    input logic       out
);
    // out matches the reduction NAND of all input bits.
    check_out_matches_reduction_nand: assert property (
        @($global_clock) out == (~(&in))
    );
endmodule

module f3_TECH_NAND2_sva (
    input logic [1:0] in,
    input logic       out
);
    // out matches the reduction NAND of all input bits.
    check_out_matches_reduction_nand: assert property (
        @($global_clock) out == (~(&in))
    );
endmodule

module f4_TECH_NAND18_sva (
    input logic [17:0] in,
    input logic        out
);
    // out matches the reduction NAND of all input bits.
    check_out_matches_reduction_nand: assert property (
        @($global_clock) out == (~(&in))
    );
endmodule

module f4_TECH_NAND4_sva (
    input logic [3:0] in,
    input logic       out
);
    // out matches the reduction NAND of all input bits.
    check_out_matches_reduction_nand: assert property (
        @($global_clock) out == (~(&in))
    );
endmodule

module f4_TECH_NAND2_sva (
    input logic [1:0] in,
    input logic       out
);
    // out matches the reduction NAND of all input bits.
    check_out_matches_reduction_nand: assert property (
        @($global_clock) out == (~(&in))
    );
endmodule

module f5_TECH_NAND18_sva (
    input logic [17:0] in,
    input logic        out
);
    // out matches the reduction NAND of all input bits.
    check_out_matches_reduction_nand: assert property (
        @($global_clock) out == (~(&in))
    );
endmodule

module f5_TECH_NAND4_sva (
    input logic [3:0] in,
    input logic       out
);
    // out matches the reduction NAND of all input bits.
    check_out_matches_reduction_nand: assert property (
        @($global_clock) out == (~(&in))
    );
endmodule

module f5_TECH_NAND2_sva (
    input logic [1:0] in,
    input logic       out
);
    // out matches the reduction NAND of all input bits.
    check_out_matches_reduction_nand: assert property (
        @($global_clock) out == (~(&in))
    );
endmodule

module f6_TECH_NOR18_sva (
    input logic [17:0] in,
    input logic        out
);
    // out matches the reduction NOR of all input bits.
    check_out_matches_reduction_nor: assert property (
        @($global_clock) out == (~(|in))
    );
endmodule

module f6_TECH_NOR4_sva (
    input logic [3:0] in,
    input logic       out
);
    // out matches the reduction NOR of all input bits.
    check_out_matches_reduction_nor: assert property (
        @($global_clock) out == (~(|in))
    );
endmodule

module f6_TECH_NOR2_sva (
    input logic [1:0] in,
    input logic       out
);
    // out matches the reduction NOR of all input bits.
    check_out_matches_reduction_nor: assert property (
        @($global_clock) out == (~(|in))
    );
endmodule

module f7_TECH_NOR18_sva (
    input logic [17:0] in,
    input logic        out
);
    // out matches the reduction NOR of all input bits.
    check_out_matches_reduction_nor: assert property (
        @($global_clock) out == (~(|in))
    );
endmodule

module f7_TECH_NOR4_sva (
    input logic [3:0] in,
    input logic       out
);
    // out matches the reduction NOR of all input bits.
    check_out_matches_reduction_nor: assert property (
        @($global_clock) out == (~(|in))
    );
endmodule

module f7_TECH_NOR2_sva (
    input logic [1:0] in,
    input logic       out
);
    // out matches the reduction NOR of all input bits.
    check_out_matches_reduction_nor: assert property (
        @($global_clock) out == (~(|in))
    );
endmodule

module f8_TECH_NOR18_sva (
    input logic [17:0] in,
    input logic        out
);
    // out matches the reduction NOR of all input bits.
    check_out_matches_reduction_nor: assert property (
        @($global_clock) out == (~(|in))
    );
endmodule

module f8_TECH_NOR4_sva (
    input logic [3:0] in,
    input logic       out
);
    // out matches the reduction NOR of all input bits.
    check_out_matches_reduction_nor: assert property (
        @($global_clock) out == (~(|in))
    );
endmodule

module f8_TECH_NOR2_sva (
    input logic [1:0] in,
    input logic       out
);
    // out matches the reduction NOR of all input bits.
    check_out_matches_reduction_nor: assert property (
        @($global_clock) out == (~(|in))
    );
endmodule

module f9_TECH_OR18_sva (
    input logic [17:0] in,
    input logic        out
);
    // out matches the reduction OR of all input bits.
    check_out_matches_reduction_or: assert property (
        @($global_clock) out == (|in)
    );
endmodule

module f9_TECH_OR4_sva (
    input logic [3:0] in,
    input logic       out
);
    // out matches the reduction OR of all input bits.
    check_out_matches_reduction_or: assert property (
        @($global_clock) out == (|in)
    );
endmodule

module f10_TECH_OR5_sva (
    input logic [4:0] in,
    input logic       out
);
    // out matches the reduction OR of all input bits.
    check_out_matches_reduction_or: assert property (
        @($global_clock) out == (|in)
    );
endmodule

module f11_TECH_XOR5_sva (
    input logic [4:0] in,
    input logic       out
);
    // out matches the five-input XOR of the input bits.
    check_out_matches_xor_chain: assert property (
        @($global_clock) out == (in[0] ^ in[1] ^ in[2] ^ in[3] ^ in[4])
    );
endmodule

module f11_TECH_XOR2_sva (
    input logic [1:0] in,
    input logic       out
);
    // out matches the two-input XOR of the input bits.
    check_out_matches_xor_chain: assert property (
        @($global_clock) out == (in[0] ^ in[1])
    );
endmodule

module f12_TECH_XOR5_sva (
    input logic [4:0] in,
    input logic       out
);
    // out matches the five-input XOR of the input bits.
    check_out_matches_xor_chain: assert property (
        @($global_clock) out == (in[0] ^ in[1] ^ in[2] ^ in[3] ^ in[4])
    );
endmodule

module f12_TECH_XOR2_sva (
    input logic [1:0] in,
    input logic       out
);
    // out matches the two-input XOR of the input bits.
    check_out_matches_xor_chain: assert property (
        @($global_clock) out == (in[0] ^ in[1])
    );
endmodule

module f13_TECH_XOR2_sva (
    input logic [1:0] in,
    input logic       out
);
    // out matches the two-input XOR of the input bits.
    check_out_matches_xor_chain: assert property (
        @($global_clock) out == (in[0] ^ in[1])
    );
endmodule

module f14_TECH_XOR5_sva (
    input logic [4:0] in,
    input logic       out
);
    // out matches the five-input XOR of the input bits.
    check_out_matches_xor_chain: assert property (
        @($global_clock) out == (in[0] ^ in[1] ^ in[2] ^ in[3] ^ in[4])
    );
endmodule

module f14_TECH_XOR2_sva (
    input logic [1:0] in,
    input logic       out
);
    // out matches the two-input XOR of the input bits.
    check_out_matches_xor_chain: assert property (
        @($global_clock) out == (in[0] ^ in[1])
    );
endmodule

module f15_TECH_XOR5_sva (
    input logic [4:0] in,
    input logic       out
);
    // out matches the five-input XOR of the input bits.
    check_out_matches_xor_chain: assert property (
        @($global_clock) out == (in[0] ^ in[1] ^ in[2] ^ in[3] ^ in[4])
    );
endmodule

module f15_TECH_XOR2_sva (
    input logic [1:0] in,
    input logic       out
);
    // out matches the two-input XOR of the input bits.
    check_out_matches_xor_chain: assert property (
        @($global_clock) out == (in[0] ^ in[1])
    );
endmodule