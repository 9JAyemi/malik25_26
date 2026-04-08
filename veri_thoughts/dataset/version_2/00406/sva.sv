module oh_reg1_sva #(parameter DW = 1) (
    input logic          nreset,
    input logic          clk,
    input logic          en,
    input logic [DW-1:0] in,
    input logic [DW-1:0] out
);

    // Active-low reset forces the output to zero.
    check_reset_forces_zero: assert property (
        @(posedge clk) !nreset |-> (out == '0)
    );

    // On a sampled reset release, the output is still zero before any new write.
    check_reset_release_starts_zero: assert property (
        @(posedge clk) disable iff (!nreset) $rose(nreset) |-> (out == '0)
    );

    // With enable low, the output holds unless async reset clears it to zero.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!nreset)
        !en |=> ((out == $past(out)) || (out == '0))
    );

    // With enable high, the next sampled output reflects the input unless async reset clears it.
    check_capture_when_enabled: assert property (
        @(posedge clk) disable iff (!nreset)
        en |=> ((out == $past(in)) || (out == '0))
    );

endmodule