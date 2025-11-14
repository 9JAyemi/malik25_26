// SVA for sky130_fd_sc_hvl__o22ai
// Function: Y = ~((A1|A2) & (B1|B2)) = ~(A1|A2) | ~(B1|B2)

module o22ai_sva (
  input logic Y,
  input logic A1, A2, B1, B2,
  input logic VPWR, VGND, VPB, VNB,
  input logic nor0_out, nor1_out, or0_out_Y
);

  function automatic bit known(input logic s); return !$isunknown(s); endfunction
  function automatic bit all_known4(input logic a,b,c,d);
    return known(a)&&known(b)&&known(c)&&known(d);
  endfunction

  logic pwr_good;
  assign pwr_good = (VPWR===1'b1) && (VPB===1'b1) && (VGND===1'b0) && (VNB===1'b0);

  // Power pins must be sane
  apwr_const: assert property (@(*)) (VPWR===1'b1 && VPB===1'b1 && VGND===1'b0 && VNB===1'b0);

  // Functional equivalence (allow 0-delay settle with ##0)
  a_func: assert property (@(*)
    disable iff (!pwr_good)
    all_known4(A1,A2,B1,B2) |-> ##0 (Y === (~((A1|A2) & (B1|B2))))
  );

  // No X on Y when inputs known and power good
  a_no_x_y: assert property (@(*)
    disable iff (!pwr_good)
    all_known4(A1,A2,B1,B2) |-> ##0 (! $isunknown(Y))
  );

  // Internal structural checks
  a_nor0: assert property (@(*)
    disable iff (!pwr_good)
    known(B1) && known(B2) |-> ##0 (nor0_out === ~(B1|B2))
  );
  a_nor1: assert property (@(*)
    disable iff (!pwr_good)
    known(A1) && known(A2) |-> ##0 (nor1_out === ~(A1|A2))
  );
  a_or0: assert property (@(*)
    disable iff (!pwr_good)
    known(nor0_out) && known(nor1_out) |-> ##0 (or0_out_Y === (nor0_out | nor1_out))
  );
  a_buf: assert property (@(*)
    disable iff (!pwr_good)
    known(or0_out_Y) |-> ##0 (Y === or0_out_Y)
  );

  // Coverage: all 16 input combinations under good power and known inputs
  genvar i;
  generate
    for (i=0; i<16; i++) begin : COV_TT
      cover property (@(*)
        pwr_good && all_known4(A1,A2,B1,B2) && ({A1,A2,B1,B2} === i[3:0])
      );
    end
  endgenerate

  // Coverage: Y toggles
  c_y_rise: cover property (@(*)) pwr_good && $rose(Y);
  c_y_fall: cover property (@(*)) pwr_good && $fell(Y);

endmodule

bind sky130_fd_sc_hvl__o22ai o22ai_sva o22ai_sva_i (.*);