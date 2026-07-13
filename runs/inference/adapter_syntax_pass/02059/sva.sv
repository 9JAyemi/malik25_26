module top_module_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic sel,
    input logic [3:0] OUT
);

    // OUT must match the muxed path from the RTL.
    check_out_matches_mux_path: assert property (
        @(posedge clk)
        OUT == (sel ? ~A + 4'd1 : B)
    );

    // When sel is low, OUT must equal B.
    check_out_equals_b_when_sel_low: assert property (
        @(posedge clk)
        !sel |-> (OUT == B)
    );

    // When sel is high, OUT must equal the 4-bit two's complement of A.
    check_out_equals_twos_comp_when_sel_high: assert property (
        @(posedge clk)
        sel |-> (OUT == (~A + 4'd1))
    );

    // The top-level output must always be either B or the two's complement of A.
    check_out_is_b_or_twos_comp: assert property (
        @(posedge clk)
        (OUT == B) || (OUT == (~A + 4'd1))
    );

endmodule