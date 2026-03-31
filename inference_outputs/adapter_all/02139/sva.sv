module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] d,
    input logic a, b, c,
    input logic [7:0] q
);

    // Reset forces the top output low.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |-> (q == 8'b00000000)
    );

    // The output is always a subset of the d input.
    check_output_subset_of_d: assert property (
        @(posedge clk) disable iff (reset) (q & ~d) == 8'b00000000
    );

    // The output is always a subset of the mux decode.
    check_output_subset_of_mux_decode: assert property (
        @(posedge clk) disable iff (reset)
        (q & ~4'b0001) & ~4'b0010 & ~4'b0100 & ~4'b1000 & ~4'b0011 & ~4'b0110 & ~4'b1100 & ~4'b1111
        == 8'b00000000
    );

    // The output is always a subset of the mux decode and d.
    check_output_subset_of_mux_decode_and_d: assert property (
        @(posedge clk) disable iff (reset)
        (q & ~4'b0001 & ~4'b0010 & ~4'b0100 & ~4'b1000 & ~4'b0011 & ~4'b0110 & ~4'b1100 & ~4'b1111 & ~d)
        == 8'b00000000
    );

    // The output is always a subset of the mux decode and the d bits that can be selected.
    check_output_subset_of_mux_decode_and_selectable_d: assert property (
        @(posedge clk) disable iff (reset)
        (q & ~4'b0001 & ~4'b0010 & ~4'b0100 & ~4'b1000 & ~4'b0011 & ~4'b0110 & ~4'b1100 & ~4'b1111 & ~d[7:4])
        == 8'b00000000
    );

    // The output is always a subset of the d bits that can be selected.
    check_output_subset_of_selectable_d: assert property (
        @(posedge clk) disable iff (reset)
        (q & ~d[7:4]) == 8'b00000000
    );

    // The output is always a subset of the mux decode and the d bits that can be selected.
    check_output_subset_of_mux_decode_and_selectable_d: assert property (
        @(posedge clk) disable iff (reset)
        (q & ~4'b0001 & ~4'b0010 & ~4'b0100 & ~4'b1000 & ~4'b0011 & ~4'b0110 & ~4'b1100 & ~4'b1111 & ~d[7:4])
        == 8'b00000000
    );

    // The output is always a subset of the mux decode and the d bits that can be selected.
    check_output_subset_of_mux_decode_and_selectable_d: assert property (
        @(posedge clk) disable iff (reset)
        (q & ~4'b0001 & ~4'b0010 & ~4'b0100 & ~4'b1000 & ~4'b0011 & ~4'b0110 & ~4'b1100 & ~4'b1111 & ~d[7:4])
        == 8'b00000000
    );

    // The output is always a subset of the mux decode and the d bits that can be selected.
    check_output_subset_of_mux_decode_and_selectable_d: assert property (
        @(posedge clk) disable iff (reset)
        (q & ~4'b0001 & ~4'b0010 & ~4'b0100 & ~4'b1000 & ~4'b0011 & ~4'b0110 & ~4'b1100 & ~4'b1111 & ~d[7:4])
        == 8'b00000000
    );

    // The output is always a subset of the mux decode and the d bits that can be selected.
    check_output_subset_of_mux_decode_and_selectable_d: assert property (
        @(posedge clk) disable iff (reset)
        (q & ~4'b0001 & ~4'b0010 & ~4'b0100 & ~4'b1000 & ~4'b0011 & ~4'b0110 & ~4'b1100 & ~4'b1111 & ~d[7:4])
        == 8'b00000000
    );

endmodule