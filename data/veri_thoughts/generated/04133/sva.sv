module mux_256to1_sva (
    input logic clk,
    input logic [255:0] in,
    input logic [7:0] sel,
    input logic out
);

    // Output must always match the RTL mux expression.
    check_out_matches_rtl_function: assert property (
        @(posedge clk) out == (sel[7] ? in[sel[6:0]] : 1'b0)
    );

    // When the select MSB is low, the output is forced low.
    check_out_zero_when_sel_msb_low: assert property (
        @(posedge clk) !sel[7] |-> (out == 1'b0)
    );

    // When the select MSB is high, the output matches the indexed input bit.
    check_out_matches_selected_input_when_enabled: assert property (
        @(posedge clk) sel[7] |-> (out == in[sel[6:0]])
    );

    // If select and the reachable input bits are unchanged, the output stays unchanged.
    check_out_stable_when_relevant_inputs_stable: assert property (
        @(posedge clk) ($stable(sel) && $stable(in[127:0])) |-> $stable(out)
    );

endmodule