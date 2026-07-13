module mux4to1_sva (
    input logic clk,        // External clock for sampling assertions (RTL has no clock/reset)
    input logic [3:0] in,
    input logic [1:0] sel,
    input logic out
);
    // Out equals the input bit indexed by sel.
    check_out_matches_index: assert property (
        @(posedge clk) out == in[sel]
    );

    // When sel==00, out must equal in[0].
    check_sel_00_mapping: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == in[0])
    );

    // When sel==01, out must equal in[1].
    check_sel_01_mapping: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == in[1])
    );

    // When sel==10, out must equal in[2].
    check_sel_10_mapping: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == in[2])
    );

    // When sel==11, out must equal in[3].
    check_sel_11_mapping: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == in[3])
    );

    // Out equals SOP decode of sel and inputs (structural equivalence).
    check_sop_equivalence: assert property (
        @(posedge clk) out ==
            ((~sel[1] & ~sel[0] & in[0]) |
             (~sel[1] &  sel[0] & in[1]) |
             ( sel[1] & ~sel[0] & in[2]) |
             ( sel[1] &  sel[0] & in[3]))
    );
endmodule