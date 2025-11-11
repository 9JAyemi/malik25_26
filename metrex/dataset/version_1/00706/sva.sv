// SVA for idec. Concise equivalence checks plus focused functional coverage.
// Provide a sampling clock with period > module's #1 comb delay.

module idec_sva (
  input logic clk,
  // DUT ports
  input logic [3:0] aluf,readAddrA,readAddrB,writeAddress,
  input logic [1:0] selA,selB,
  input logic clrR, clrIr0, gate, rw, sel_addr_reg, dojump, wrAddr,
  input logic [15:0] ir0q,ir1q,
  input logic [3:0] flags,
  input logic reset
);

  default clocking cb @(posedge clk); endclocking

  // Local re-implementation of jmpchk
  function automatic logic loc_jmpchk (logic [2:0] condition, logic [3:0] flags_i);
    logic sign,carry,parity,zero;
    {sign,carry,parity,zero} = flags_i;
    unique case (condition)
      3'b000: loc_jmpchk = 1'b1;
      3'b001: loc_jmpchk = ~sign;
      3'b010: loc_jmpchk =  sign;
      3'b011: loc_jmpchk =  zero;
      3'b100: loc_jmpchk =  parity;
      3'b101: loc_jmpchk =  carry;
      3'b110: loc_jmpchk = ~carry;
      3'b111: loc_jmpchk = ~zero;
    endcase
  endfunction

  // Known-value check: if inputs known, outputs known
  assert property (!$isunknown({ir0q,ir1q,flags,reset}) |-> !$isunknown({
                    aluf,readAddrA,readAddrB,writeAddress,selA,selB,
                    clrR,clrIr0,gate,rw,sel_addr_reg,dojump,wrAddr}));

  // Direct functional equivalence checks
  assert property (aluf        == ir1q[15:12]);
  assert property (readAddrA   == ir0q[11:8]);
  assert property (readAddrB   == ir0q[ 7:4]);
  assert property (writeAddress== ir1q[11:8]);

  assert property (selA == (readAddrA[3:2] != 2'b00 ? 2'b11 : readAddrA[1:0]));
  assert property (selB == (readAddrB[3:2] != 2'b00 ? 2'b11 : readAddrB[1:0]));

  assert property (sel_addr_reg ==
                   ((ir0q[3] & (ir0q[7:4]  == 4'h0)) |
                    (ir1q[3] & (ir1q[11:8] == 4'h0))));

  assert property (rw == ~(ir1q[3] & (ir1q[11:8] == 4'h0)));

  assert property (dojump == (loc_jmpchk(ir1q[2:0], flags) & (ir1q[11:8] == 4'h1)));
  assert property (wrAddr == (ir1q[11:8] == 4'h2));

  assert property (gate == (|aluf));
  assert property (clrR == reset);

  assert property (clrIr0 == (reset | dojump
                              | ((ir0q[7:4] == 4'h0) & (ir0q[11:8] != 4'h0))
                              | ~rw));

  // A few helpful implications
  assert property (dojump |-> (ir1q[11:8] == 4'h1));
  assert property ((ir1q[3] && (ir1q[11:8]==4'h0)) |-> (!rw && sel_addr_reg));
  assert property ((ir0q[3] && (ir0q[7:4]==4'h0))  |-> sel_addr_reg);

  // Coverage: exercise key features and each jump condition outcome
  cover property ((aluf != 4'h0) && gate);
  cover property ((aluf == 4'h0) && !gate);

  cover property (rw);
  cover property (!rw);

  cover property (wrAddr && (ir1q[11:8]==4'h2));

  cover property ((ir0q[3] && (ir0q[7:4]==4'h0))  && sel_addr_reg); // m0 path
  cover property ((ir1q[3] && (ir1q[11:8]==4'h0)) && sel_addr_reg); // m1 path

  cover property ((readAddrA[3:2]!=2'b00) && selA==2'b11);
  cover property ((readAddrA[3:2]==2'b00) && selA==readAddrA[1:0]);
  cover property ((readAddrB[3:2]!=2'b00) && selB==2'b11);
  cover property ((readAddrB[3:2]==2'b00) && selB==readAddrB[1:0]);

  // clrIr0 individual causes
  cover property (reset  && clrIr0);
  cover property (dojump && clrIr0);
  cover property (((ir0q[7:4]==4'h0) && (ir0q[11:8]!=4'h0)) && clrIr0);
  cover property ((!rw) && clrIr0);

  // dojump per-condition: cover both taken and not-taken
  genvar i;
  generate
    for (i=0;i<8;i++) begin : C_JMP
      cover property ((ir1q[11:8]==4'h1) && (ir1q[2:0]==i[2:0]) &&
                      loc_jmpchk(ir1q[2:0],flags) && dojump);
      cover property ((ir1q[11:8]==4'h1) && (ir1q[2:0]==i[2:0]) &&
                      !loc_jmpchk(ir1q[2:0],flags) && !dojump);
    end
  endgenerate

endmodule

// Example bind (replace tb_clk with your sampling clock):
// bind idec idec_sva sva ( .clk(tb_clk), .aluf(aluf), .readAddrA(readAddrA), .readAddrB(readAddrB),
//   .writeAddress(writeAddress), .selA(selA), .selB(selB), .clrR(clrR), .clrIr0(clrIr0), .gate(gate),
//   .rw(rw), .sel_addr_reg(sel_addr_reg), .dojump(dojump), .wrAddr(wrAddr),
//   .ir0q(ir0q), .ir1q(ir1q), .flags(flags), .reset(reset) );