module register_clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // Analysis: clock=CLK; no reset in RTL; logic is purely combinational; behavior: ENCLK = (TE ? CLK : EN).

    // ENCLK implements the exact mux function defined by RTL.
    check_functional_mux: assert property (
        @(posedge CLK) ENCLK == (TE ? CLK : EN)
    );

    // When TE=1, ENCLK must mirror CLK.
    check_te_selects_clk: assert property (
        @(posedge CLK) TE |-> (ENCLK == CLK)
    );

    // When TE=0, ENCLK must equal EN.
    check_te0_selects_en: assert property (
        @(posedge CLK) !TE |-> (ENCLK == EN)
    );

    // If ENCLK is LOW at CLK posedge, then TE=0 and EN=0.
    check_out_low_conditions: assert property (
        @(posedge CLK) (ENCLK == 1'b0) |-> (!TE && (EN == 1'b0))
    );

    // If ENCLK is HIGH at CLK posedge, then TE=1 or EN=1.
    check_out_high_conditions: assert property (
        @(posedge CLK) (ENCLK == 1'b1) |-> (TE || (EN == 1'b1))
    );
endmodule