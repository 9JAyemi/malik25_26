module mux_dff_sva (
    input logic CLK,
    input logic Q,
    input logic Q_N,
    input logic D,
    input logic SCD,
    input logic SCE
);
    // Sequential logic: DFF
    // Q should be equal to D at the rising edge of CLK
    dff_property: assert property (
        @(posedge CLK) disable iff (!CLK) Q == D
    );

    // Combinational logic: Mux4to1
    // buf_D should be equal to D
    buf_D_property: assert property (
        @(posedge CLK) disable iff (!CLK) buf_D == D
    );

    // Combinational logic: Mux4to1
    // buf_mux_out should be equal to the output of the mux4to1 module
    buf_mux_out_property: assert property (
        @(posedge CLK) disable iff (!CLK) buf_mux_out == (SCD) ? D : (SCE) ? 1'b0 : 1'b0
    );

    // Combinational logic: Mux4to1
    // mux_out should be equal to the output of the mux4to1 module
    mux_out_property: assert property (
        @(posedge CLK) disable iff (!CLK) mux_out == (SCD) ? D : (SCE) ? 1'b0 : 1'b0
    );

    // Combinational logic: Mux4to1
    // D_out should be equal to the output of the mux4to1 module
    D_out_property: assert property (
        @(posedge CLK) disable iff (!CLK) D_out == (SCD) ? D : (SCE) ? 1'b0 : 1'b0
    );

    // Combinational logic: Not gates
    // not_SCD should be the negation of SCD
    not_SCD_property: assert property (
        @(posedge CLK) disable iff (!CLK) not_SCD == ~SCD
    );

    // Combinational logic: Not gates
    // not_SCE should be the negation of SCE
    not_SCE_property: assert property (
        @(posedge CLK) disable iff (!CLK) not_SCE == ~SCE
    );

    // Combinational logic: And gates
    // and_SCD_not_SCE should be the AND of SCD and not_SCE
    and_SCD_not_SCE_property: assert property (
        @(posedge CLK) disable iff (!CLK) and_SCD_not_SCE == SCD & not_SCE
    );

    // Combinational logic: And gates
    // and_not_SCD_SCE should be the AND of not_SCD and SCE
    and_not_SCD_SCE_property: assert property (
        @(posedge CLK) disable iff (!CLK) and_not_SCD_SCE == not_SCD & SCE
    );

    // Combinational logic: And gates
    // and_SCD_SCE should be the AND of SCD and SCE
    and_SCD_SCE_property: assert property (
        @(posedge CLK) disable iff (!CLK) and_SCD_SCE == SCD & SCE
    );

    // Combinational logic: And gates
    // and_not_SCD_not_SCE should be the AND of not_SCD and not_SCE
    and_not_SCD_not_SCE_property: assert property (
        @(posedge CLK) disable iff (!CLK) and_not_SCD_not_SCE == not_SCD & not_SCE
    );

    // Combinational logic: Not gates
    // not_Q0 should be the negation of buf_mux_out
    not_Q0_property: assert property (
        @(posedge CLK) disable iff (!CLK) Q_N == ~buf_mux_out
    );

    // Combinational logic: Buffer gates
    // buf_Q0 should be equal to buf_mux_out
    buf_Q0_property: assert property (
        @(posedge CLK) disable iff (!CLK) Q == buf_mux_out
    );
endmodule