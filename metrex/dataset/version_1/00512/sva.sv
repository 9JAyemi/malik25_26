// SVA for ALU
// Bind this checker into ALU to access internals
module ALU_sva();
  default clocking cb @(posedge clk); endclocking

  // adder_CI gating
  assert property ( (right || (op[3:2]==2'b11)) |-> adder_CI==1'b0 );
  assert property ( (!right && (op[3:2]!=2'b11)) |-> adder_CI==CI );

  // temp_logic formation
  assert property ( right |-> temp_logic == {AI[0], CI, AI[7:1]} );
  assert property ( !right && (op[1:0]==2'b00) |-> (temp_logic[7:0]==(AI|BI)  && temp_logic[8]==1'b0) );
  assert property ( !right && (op[1:0]==2'b01) |-> (temp_logic[7:0]==(AI&BI)  && temp_logic[8]==1'b0) );
  assert property ( !right && (op[1:0]==2'b10) |-> (temp_logic[7:0]==(AI^BI)  && temp_logic[8]==1'b0) );
  assert property ( !right && (op[1:0]==2'b11) |-> (temp_logic[7:0]== AI     && temp_logic[8]==1'b0) );

  // temp_BI selection (note: width truncation from temp_logic)
  assert property ( (op[3:2]==2'b00) |-> temp_BI== BI );
  assert property ( (op[3:2]==2'b01) |-> temp_BI== ~BI );
  assert property ( (op[3:2]==2'b10) |-> temp_BI== temp_logic[7:0] );
  assert property ( (op[3:2]==2'b11) |-> temp_BI== 8'h00 );

  // Nibble sums and BCD-related carries
  assert property ( temp_l == (temp_logic[3:0] + temp_BI[3:0] + adder_CI) );
  assert property ( temp_h == (temp_logic[8:4] + temp_BI[7:4] + temp_HC) );
  assert property ( HC9 == (BCD && (temp_l[3:1] >= 3'd5)) );
  assert property ( CO9 == (BCD && (temp_h[3:1] >= 3'd5)) );
  assert property ( temp_HC == (temp_l[4] || HC9) );

  // Sequential updates when RDY
  assert property ( RDY |-> ##0 (OUT == temp[7:0] && CO == (temp[8] | CO9) && N == temp[7] && HC == temp_HC && AI7 == AI[7] && BI7 == temp_BI[7]) );

  // Hold registers when !RDY
  assert property ( !RDY |-> ($stable(OUT) && $stable(CO) && $stable(N) && $stable(HC) && $stable(AI7) && $stable(BI7)) );

  // Continuous flag definitions (post-NBA sampling)
  assert property ( ##0 Z == ~|OUT );
  assert property ( ##0 V == (AI7 ^ BI7 ^ CO ^ N) );

  // Basic X-checks on outputs when RDY
  assert property ( RDY |-> ##0 (!$isunknown({OUT,CO,N,HC,V,Z})) );

  // Coverage
  cover property ( RDY && !right && op[1:0]==2'b00 );
  cover property ( RDY && !right && op[1:0]==2'b01 );
  cover property ( RDY && !right && op[1:0]==2'b10 );
  cover property ( RDY && !right && op[1:0]==2'b11 );
  cover property ( RDY && (op[3:2]==2'b00) );
  cover property ( RDY && (op[3:2]==2'b01) );
  cover property ( RDY && (op[3:2]==2'b10) );
  cover property ( RDY && (op[3:2]==2'b11) );
  cover property ( RDY && right );
  cover property ( RDY && BCD && HC9 );
  cover property ( RDY && BCD && CO9 );
  cover property ( RDY && Z );
  cover property ( RDY && N );
  cover property ( RDY && V );
  cover property ( RDY && CO );
  cover property ( RDY && adder_CI==1'b0 );
  cover property ( RDY && adder_CI==1'b1 );
endmodule

bind ALU ALU_sva ALU_sva_i();