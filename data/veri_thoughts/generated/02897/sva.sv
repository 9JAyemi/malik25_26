module mux4_sva (
    // DUT mux4 ports
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic sel0,
    input logic sel1,
    input logic [3:0] out,
    // Sampling clock/reset (DUT is pure combinational; these are for assertions only)
    input logic CLK,
    input logic RESETn
);
    // Output equals in0 when sel1=0 and sel0=0.
    check_out_sel00: assert property (
        @(posedge CLK) disable iff (!RESETn) (!sel1 && !sel0) |-> (out == in0)
    );

    // Output equals in1 when sel1=0 and sel0=1.
    check_out_sel01: assert property (
        @(posedge CLK) disable iff (!RESETn) (!sel1 && sel0) |-> (out == in1)
    );

    // Output equals in2 when sel1=1 and sel0=0.
    check_out_sel10: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel1 && !sel0) |-> (out == in2)
    );

    // Output equals in3 when sel1=1 and sel0=1.
    check_out_sel11: assert property (
        @(posedge CLK) disable iff (!RESETn) (sel1 && sel0) |-> (out == in3)
    );

    // Output matches the RTL ternary expression for all select combinations.
    check_out_expr_equivalence: assert property (
        @(posedge CLK) disable iff (!RESETn)
            out == ( (sel1 & sel0) ? in3
                  : (sel1 & ~sel0) ? in2
                  : (~sel1 & sel0) ? in1
                  : in0 )
    );
endmodule