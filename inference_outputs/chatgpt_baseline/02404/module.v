
module mux_dff (
    Q  ,
    Q_N,
    CLK,
    D  ,
    SCD,
    SCE
);

    // Module ports
    output Q  ;
    output Q_N;
    input  CLK;
    input  D  ;
    input  SCD;
    input  SCE;

    // Local signals
    wire buf_D  ;
    wire buf_mux_out ;
    wire and_SCD_not_SCE ;
    wire and_not_SCD_SCE ;
    wire and_SCD_SCE ;
    wire not_SCD ;
    wire not_SCE ;
    wire and_not_SCD_not_SCE ;
    wire mux_out ;
    wire D_out ; 

    // Gates
    buf buf_D0 (buf_D, D);
    not not_SCD0 (not_SCD, SCD);
    not not_SCE0 (not_SCE, SCE);
    and and_SCD_not_SCE0 (and_SCD_not_SCE, SCD, not_SCE);
    and and_not_SCD_SCE0 (and_not_SCD_SCE, not_SCD, SCE);
    and and_SCD_SCE0 (and_SCD_SCE, SCD, SCE);
    and and_not_SCD_not_SCE0 (and_not_SCD_not_SCE, not_SCD, not_SCE);
    mux4to1 mux_4to10 (mux_out, buf_D, buf_mux_out, and_SCD_not_SCE, and_not_SCD_SCE);
    dff dff0 (buf_mux_out, mux_out, CLK);
    not not_Q0 (Q_N, buf_mux_out);
    buf buf_Q0 (Q, buf_mux_out);

endmodule
module mux4to1(
  output mux_out,
  input  in_0,
  input  in_1,
  input  sel_0,
  input  sel_1
);

  assign mux_out = (sel_0) ? (in_0) :
                    (sel_1) ? (in_1) :
                    1'b0;

endmodule
module dff(
  output  Q,
  input   D,
  input   CLK
);

  reg     Q_reg;

  always @(posedge CLK) begin
    Q_reg <= D;
  end

  assign Q = Q_reg;

endmodule