module top_module_sva (
    input logic [1023:0] in,
    input logic [7:0]    sel,
    input logic [3:0]    out
);

    // out must equal the 4-bit slice of in selected by sel.
    check_out_selects_requested_nibble: assert property (
        @($global_clock) out === in[(sel * 4) +: 4]
    );

endmodule