// SVA for sky130_fd_sc_ls__or4b
// Concise, power-aware, full functional checks and input-space coverage.

module sky130_fd_sc_ls__or4b_sva (
    input  A, B, C, D_N,
    input  X,
    input  VPB, VPWR, VGND, VNB,
    // internal nets
    input  AB_w, CD_N_w, ABCD_N_w
);
    // Power-good definition
    wire pgood = (VPWR === 1'b1) && (VGND === 1'b0) && (VPB === 1'b1) && (VNB === 1'b0);

    // Combinational functional checks (guarded by power-good and known inputs)
    always @* begin
        if (pgood && !$isunknown({A,B,C,D_N})) begin
            assert #0 (AB_w     === (A | B))                      else $error("AB mismatch");
            assert #0 (CD_N_w   === (C | D_N))                    else $error("CD_N mismatch");
            assert #0 (ABCD_N_w === (AB_w | CD_N_w))              else $error("ABCD_N mismatch");
            assert #0 (X        === ~ABCD_N_w)                    else $error("X != ~ABCD_N");
            assert #0 (X        === ~(A | B | C | D_N))           else $error("X != ~(A|B|C|D_N)");
            assert #0 (!$isunknown(X))                            else $error("X unknown with valid power and known inputs");
        end
    end

    // Simple output-state coverage under valid power and known inputs
    always @* if (pgood && !$isunknown({A,B,C,D_N})) begin
        cover (X === 1'b1);
        cover (X === 1'b0);
    end

    // Full input-space coverage (all 16 combinations) under valid power
    genvar i;
    generate
        for (i = 0; i < 16; i++) begin : g_in_cov
            always @* if (pgood) cover ({A,B,C,D_N} === i[3:0]);
        end
    endgenerate
endmodule

bind sky130_fd_sc_ls__or4b sky130_fd_sc_ls__or4b_sva
(
    .A(A), .B(B), .C(C), .D_N(D_N),
    .X(X),
    .VPB(VPB), .VPWR(VPWR), .VGND(VGND), .VNB(VNB),
    .AB_w(AB), .CD_N_w(CD_N), .ABCD_N_w(ABCD_N)
);