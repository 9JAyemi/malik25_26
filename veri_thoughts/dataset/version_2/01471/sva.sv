module clock_mux_sva #(
    parameter int n = 4
) (
    input  logic [n-1:0] clk,
    input  logic         sel,
    input  logic         clk_out
);
    // Selected clock rising drives clk_out high by the next selected edge.
    selected_edge_sets_high: assert property (
        @(posedge clk[sel]) 1 |=> (clk_out == 1'b1)
    );

    // clk_out rises only when the currently selected input is HIGH at that time.
    clk_out_rise_matches_selected_high: assert property (
        @(posedge clk_out) (clk[sel] == 1'b1)
    );

    // clk_out never falls (design never assigns it low); check on all input clock edges.
    genvar i;
    generate
        for (i = 0; i < n; i++) begin : check_no_clk_out_fall_on_any_clk
            no_fall_on_clk_i: assert property (
                @(posedge clk[i]) !$fell(clk_out)
            );
        end
    endgenerate
endmodule