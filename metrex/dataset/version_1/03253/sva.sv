// SVA for lmcnt — concise but comprehensive
module lmcnt_sva(
  input logic        CLK,
  input logic        rst_x,        // internal: RESET_X & ~SOFT_RESET
  input logic        RESET_X,
  input logic        SOFT_RESET,
  input logic        START,
  input logic        LM_EN,

  input logic [1:0]  MSEL_INPUTA_SEL,
  input logic [1:0]  MSEL_INPUTB_SEL,
  input logic [1:0]  MSEL_OUTPUTC_SEL,

  input logic [9:0]  rcnt,         // internal
  input logic [9:0]  wcnt,         // internal

  input logic        NPU_EN,
  input logic        FINISH,

  input logic [7:0]  A_RDATA,
  input logic [7:0]  B_RDATA,

  input logic [7:0]  M0_RDATA,
  input logic [7:0]  M1_RDATA,
  input logic [7:0]  M2_RDATA,
  input logic [7:0]  M3_RDATA,

  input logic        M1_WR,
  input logic        M2_WR,
  input logic        M3_WR,
  input logic [9:0]  M1_RADR,
  input logic [9:0]  M2_RADR,
  input logic [9:0]  M3_RADR,
  input logic [9:0]  M1_WADR,
  input logic [9:0]  M2_WADR,
  input logic [9:0]  M3_WADR,
  input logic [7:0]  M1_WDATA,
  input logic [7:0]  M2_WDATA,
  input logic [7:0]  M3_WDATA,
  input logic [7:0]  C_WDATA
);
  default clocking cb @(posedge CLK); endclocking
  default disable iff (!rst_x);

  localparam int unsigned MAX = 10'h3FF;

  // Control signals cleanliness
  assert property (!$isunknown(MSEL_INPUTA_SEL));
  assert property (!$isunknown(MSEL_INPUTB_SEL));
  assert property (!$isunknown(MSEL_OUTPUTC_SEL));

  // Asynchronous reset state (override default disable for this check)
  assert property (disable iff (1'b0)
                   (!rst_x |-> (rcnt==0 && wcnt==0 && NPU_EN==0 && FINISH==0 && A_RDATA==0 && B_RDATA==0)));

  // rcnt behavior
  assert property ((rcnt==0 && !START) |=> rcnt==0);
  assert property ((rcnt==0 &&  START) |=> rcnt==10'd1);
  assert property ((rcnt>0  && rcnt<MAX) |=> rcnt==$past(rcnt)+1);
  assert property ((rcnt==MAX) |=> rcnt==MAX);

  // NPU_EN behavior
  assert property (START |=> NPU_EN);
  assert property ((rcnt>0 && rcnt<MAX) |-> NPU_EN);
  assert property ((rcnt==MAX && !START) |-> (!START)[*2] ##[1:2] !NPU_EN);

  // wcnt behavior
  assert property ( LM_EN |=> wcnt==$past(wcnt)+1 );
  assert property (!LM_EN |=> wcnt==$past(wcnt)    );

  // FINISH behavior
  assert property ($rose(FINISH) |-> $past(wcnt)==MAX);
  assert property (FINISH |=> FINISH); // sticky until reset

  // Read addresses follow rcnt
  assert property (M1_RADR==rcnt);
  assert property (M2_RADR==rcnt);
  assert property (M3_RADR==rcnt);

  // A mux (registered, 1-cycle latency)
  assert property ((MSEL_INPUTA_SEL==2'b00) |=> A_RDATA==$past(M0_RDATA));
  assert property ((MSEL_INPUTA_SEL==2'b01) |=> A_RDATA==$past(M1_RDATA));
  assert property ((MSEL_INPUTA_SEL==2'b10) |=> A_RDATA==$past(M2_RDATA));
  assert property ((MSEL_INPUTA_SEL==2'b11) |=> A_RDATA==$past(M3_RDATA));

  // B mux (registered, 1-cycle latency)
  assert property ((MSEL_INPUTB_SEL==2'b00) |=> B_RDATA==$past(M0_RDATA));
  assert property ((MSEL_INPUTB_SEL==2'b01) |=> B_RDATA==$past(M1_RDATA));
  assert property ((MSEL_INPUTB_SEL==2'b10) |=> B_RDATA==$past(M2_RDATA));
  assert property ((MSEL_INPUTB_SEL==2'b11) |=> B_RDATA==$past(M3_RDATA));

  // Output C routing/select
  assert property (M1_WR == (LM_EN && (MSEL_OUTPUTC_SEL==2'b01)));
  assert property (M2_WR == (LM_EN && (MSEL_OUTPUTC_SEL==2'b10)));
  assert property (M3_WR == (LM_EN && (MSEL_OUTPUTC_SEL==2'b11)));
  assert property ($onehot0({M1_WR,M2_WR,M3_WR}));
  assert property (M1_WR |-> (M1_WADR==wcnt && M1_WDATA==C_WDATA));
  assert property (M2_WR |-> (M2_WADR==wcnt && M2_WDATA==C_WDATA));
  assert property (M3_WR |-> (M3_WADR==wcnt && M3_WDATA==C_WDATA));

  // Coverage
  cover property ( (rcnt==0 && START) ##[1:$] (rcnt==MAX) ##[1:2] !NPU_EN );
  cover property ( FINISH );
  cover property ( MSEL_INPUTA_SEL==2'b00 );
  cover property ( MSEL_INPUTA_SEL==2'b01 );
  cover property ( MSEL_INPUTA_SEL==2'b10 );
  cover property ( MSEL_INPUTA_SEL==2'b11 );
  cover property ( MSEL_INPUTB_SEL==2'b00 );
  cover property ( MSEL_INPUTB_SEL==2'b01 );
  cover property ( MSEL_INPUTB_SEL==2'b10 );
  cover property ( MSEL_INPUTB_SEL==2'b11 );
  cover property ( MSEL_OUTPUTC_SEL==2'b01 && LM_EN );
  cover property ( MSEL_OUTPUTC_SEL==2'b10 && LM_EN );
  cover property ( MSEL_OUTPUTC_SEL==2'b11 && LM_EN );
endmodule

// Bind into DUT; connects internal regs/wires for strong checking
bind lmcnt lmcnt_sva u_lmcnt_sva (
  .CLK(CLK),
  .rst_x(rst_x),
  .RESET_X(RESET_X),
  .SOFT_RESET(SOFT_RESET),
  .START(START),
  .LM_EN(LM_EN),
  .MSEL_INPUTA_SEL(MSEL_INPUTA_SEL),
  .MSEL_INPUTB_SEL(MSEL_INPUTB_SEL),
  .MSEL_OUTPUTC_SEL(MSEL_OUTPUTC_SEL),
  .rcnt(rcnt),
  .wcnt(wcnt),
  .NPU_EN(NPU_EN),
  .FINISH(FINISH),
  .A_RDATA(A_RDATA),
  .B_RDATA(B_RDATA),
  .M0_RDATA(M0_RDATA),
  .M1_RDATA(M1_RDATA),
  .M2_RDATA(M2_RDATA),
  .M3_RDATA(M3_RDATA),
  .M1_WR(M1_WR),
  .M2_WR(M2_WR),
  .M3_WR(M3_WR),
  .M1_RADR(M1_RADR),
  .M2_RADR(M2_RADR),
  .M3_RADR(M3_RADR),
  .M1_WADR(M1_WADR),
  .M2_WADR(M2_WADR),
  .M3_WADR(M3_WADR),
  .M1_WDATA(M1_WDATA),
  .M2_WDATA(M2_WDATA),
  .M3_WDATA(M3_WDATA),
  .C_WDATA(C_WDATA)
);