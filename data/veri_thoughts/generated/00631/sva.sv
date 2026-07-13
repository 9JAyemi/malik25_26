module mux4to1_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] sel,
    input logic out
);
    // Output equals the selected input bit using variable index.
    check_out_equals_indexed_in: assert property (
        @(posedge clk) out == in[sel]
    );

    // For sel=00, out mirrors in[0].
    check_sel_00: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == in[0])
    );

    // For sel=01, out mirrors in[1].
    check_sel_01: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == in[1])
    );

    // For sel=10, out mirrors in[2].
    check_sel_10: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == in[2])
    );

    // For sel=11, out mirrors in[3].
    check_sel_11: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == in[3])
    );

    // Structural equivalence to the sum-of-products implementation.
    check_structural_equivalence: assert property (
        @(posedge clk)
            out == ((in[0] & ~sel[0] & ~sel[1]) |
                    (in[1] & ~sel[0] &  sel[1]) |
                    (in[2] &  sel[0] & ~sel[1]) |
                    (in[3] &  sel[0] &  sel[1]))
    );

    // If all inputs are 0, out must be 0.
    check_zero_inputs_zero_out: assert property (
        @(posedge clk) (in == 4'b0000) |-> (out == 1'b0)
    );

    // If all inputs are 1, out must be 1.
    check_allones_inputs_one_out: assert property (
        @(posedge clk) (in == 4'b1111) |-> (out == 1'b1)
    );

    // If sel and the selected input are stable, out must be stable.
    check_stability_when_sel_and_selected_stable: assert property (
        @(posedge clk) ($stable(sel) && $stable(in[sel])) |-> $stable(out)
    );

    // If sel is stable and the selected input changes, out must change.
    check_selected_change_reflects_output_change: assert property (
        @(posedge clk) ($stable(sel) && $changed(in[sel])) |-> $changed(out)
    );
endmodule