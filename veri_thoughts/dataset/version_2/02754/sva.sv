module mux_encoder_sva (
    input logic clk,
    input logic [15:0] in,
    input logic [3:0] sel,
    input logic [7:0] D,
    input logic [7:0] out,
    input logic [2:0] EN
);
    ///// Mux output rules /////
    // When sel[2]==1, out must be zero.
    check_out_zero_when_sel2: assert property (
        @(posedge clk) sel[2] |-> (out == 8'h00)
    );

    // When sel[2]==0 and sel[3]==1, out selects in[15:8].
    check_out_upper_when_sel3_and_sel2low: assert property (
        @(posedge clk) (!sel[2] && sel[3]) |-> (out == in[15+:8])
    );

    // When sel[2]==0 and sel[3]==0, out selects in[7:0].
    check_out_lower_when_sel3low_and_sel2low: assert property (
        @(posedge clk) (!sel[2] && !sel[3]) |-> (out == in[7:0])
    );

    // Out depends only on in and sel (stable in/sel implies stable out).
    check_out_function_of_in_sel_only: assert property (
        @(posedge clk) ($stable(in) && $stable(sel)) |-> (out == $past(out))
    );

    ///// Priority encoder rules (EN) /////
    // EN must equal the ternary priority chain defined on D.
    check_en_priority_chain: assert property (
        @(posedge clk)
        EN == ( D[7] ? 3'd3 :
                D[6] ? 3'd2 :
                D[5] ? 3'd1 :
                D[4] ? 3'd0 :
                D[3] ? 3'd3 :
                D[2] ? 3'd2 :
                D[1] ? 3'd1 :
                D[0] ? 3'd0 : 3'd3 )
    );

    // EN depends only on D (stable D implies stable EN).
    check_en_function_of_D_only: assert property (
        @(posedge clk) $stable(D) |-> (EN == $past(EN))
    );

    // If D[7] is set, EN must be 3 regardless of other bits.
    check_en_when_D7: assert property (
        @(posedge clk) D[7] |-> (EN == 3'd3)
    );

    // If only D[6] is the highest set bit, EN must be 2.
    check_en_when_D6_and_no_higher: assert property (
        @(posedge clk) (!D[7] && D[6]) |-> (EN == 3'd2)
    );

    // If only D[3] is the highest set bit, EN must be 3.
    check_en_when_D3_and_no_higher: assert property (
        @(posedge clk) (!D[7] && !D[6] && !D[5] && !D[4] && D[3]) |-> (EN == 3'd3)
    );

    // If all D bits are zero, EN must be 3 (default case).
    check_en_default_when_D_zero: assert property (
        @(posedge clk) (D == 8'h00) |-> (EN == 3'd3)
    );
endmodule