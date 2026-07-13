module DEMUX_sva #(
    parameter int n = 2
) (
    input logic clk,
    input logic in,
    input logic [n-1:0] sel,
    input logic [(2**n)-1:0] out
);

    localparam int OUT_W = (2**n);

    genvar i;
    generate
        for (i = 0; i < OUT_W; i = i + 1) begin : gen_demux_checks
            // When selected, this output bit matches the input.
            check_selected_path: assert property (
                @(posedge clk) (sel == i) |-> (out[i] == in)
            );

            // When not selected, this output bit stays low.
            check_unselected_zero: assert property (
                @(posedge clk) (sel != i) |-> (out[i] == 1'b0)
            );
        end
    endgenerate

    // A low input forces all outputs low.
    check_input_low_clears_all: assert property (
        @(posedge clk) (!in) |-> (out == '0)
    );

    // A high input produces exactly one asserted output.
    check_input_high_onehot: assert property (
        @(posedge clk) in |-> $onehot(out)
    );

endmodule