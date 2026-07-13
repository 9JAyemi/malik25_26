module Span12Mux_s2_h_sva (
    input logic clk,
    input logic [11:0] I,
    input logic [1:0] S,
    input logic [11:0] O
);

    // S=00 passes I directly to O.
    check_sel_00_passthrough: assert property (
        @(posedge clk) (S === 2'b00) |-> (O === I)
    );

    // S=01 passes I directly to O.
    check_sel_01_passthrough: assert property (
        @(posedge clk) (S === 2'b01) |-> (O === {I[11:0]})
    );

    // S=10 swaps the upper and lower 6-bit halves.
    check_sel_10_swap_halves: assert property (
        @(posedge clk) (S === 2'b10) |-> (O === {I[5:0], I[11:6]})
    );

    // S=11 keeps the original 6-bit half ordering.
    check_sel_11_passthrough: assert property (
        @(posedge clk) (S === 2'b11) |-> (O === {I[11:6], I[5:0]})
    );

    // Invalid 4-state select values drive O to unknown.
    check_invalid_select_unknown_output: assert property (
        @(posedge clk)
        ((S !== 2'b00) && (S !== 2'b01) && (S !== 2'b10) && (S !== 2'b11))
        |-> (O === 12'hxxx)
    );

    // If sampled inputs do not change, sampled output does not change.
    check_stable_inputs_stable_output: assert property (
        @(posedge clk) ($stable(I) && $stable(S)) |-> $stable(O)
    );

endmodule