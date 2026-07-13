module mux_sva (
    input logic        clk,
    input logic [3:0]  opA,
    input logic [3:0]  opB,
    input logic [4:0]  sum,
    input logic [1:0]  dsp_sel,
    input logic [3:0]  out,
    input logic [3:0]  opA_out,
    input logic [3:0]  opB_out,
    input logic [3:0]  sum_out,
    input logic [3:0]  cout_out
);

    // opA_out captures opA when opA changes.
    check_opa_mirror_updates: assert property (
        @(posedge clk) $changed(opA) |-> (opA_out == opA)
    );

    // opB_out captures opB when opB changes.
    check_opb_mirror_updates: assert property (
        @(posedge clk) $changed(opB) |-> (opB_out == opB)
    );

    // sum_out captures the low 4 bits of sum when sum changes.
    check_sum_low_mirror_updates: assert property (
        @(posedge clk) $changed(sum) |-> (sum_out == sum[3:0])
    );

    // cout_out encodes sum[4] into bit 0 when sum changes.
    check_sum_carry_mirror_updates: assert property (
        @(posedge clk) $changed(sum) |-> (cout_out == {3'b000, sum[4]})
    );

    // out selects sum_out on mux activity with dsp_sel = 00.
    check_out_selects_sum_path: assert property (
        @(posedge clk)
        (($changed(dsp_sel) || $changed(sum_out) || $changed(cout_out) ||
          $changed(opB_out) || $changed(opA_out)) && (dsp_sel == 2'b00))
        |-> (out == sum_out)
    );

    // out selects cout_out on mux activity with dsp_sel = 01.
    check_out_selects_carry_path: assert property (
        @(posedge clk)
        (($changed(dsp_sel) || $changed(sum_out) || $changed(cout_out) ||
          $changed(opB_out) || $changed(opA_out)) && (dsp_sel == 2'b01))
        |-> (out == cout_out)
    );

    // out selects opB_out on mux activity with dsp_sel = 10.
    check_out_selects_opb_path: assert property (
        @(posedge clk)
        (($changed(dsp_sel) || $changed(sum_out) || $changed(cout_out) ||
          $changed(opB_out) || $changed(opA_out)) && (dsp_sel == 2'b10))
        |-> (out == opB_out)
    );

    // out selects opA_out on mux activity with dsp_sel = 11.
    check_out_selects_opa_path: assert property (
        @(posedge clk)
        (($changed(dsp_sel) || $changed(sum_out) || $changed(cout_out) ||
          $changed(opB_out) || $changed(opA_out)) && (dsp_sel == 2'b11))
        |-> (out == opA_out)
    );

    // out holds its value when no mux sensitivity input changes.
    check_out_holds_without_mux_activity: assert property (
        @(posedge clk)
        !($changed(dsp_sel) || $changed(sum_out) || $changed(cout_out) ||
          $changed(opB_out) || $changed(opA_out))
        |-> $stable(out)
    );

endmodule