// SVA checkers and binds for MAIN/ALU (combinational), focused and concise

// ---------- ALU checker ----------
module ALU_sva (
  input  logic [31:0] A, B,
  input  logic [2:0]  ALU_OP,
  input  logic [31:0] F,
  input  logic        ZF, OF
);
  // sample on any combinational change
  event comb_ev;  always @* -> comb_ev;

  // 33-bit helpers to match RTL's C32 usage
  function automatic logic [32:0] add33 (input logic [31:0] a,b);
    add33 = {1'b0,a} + {1'b0,b};
  endfunction
  function automatic logic [32:0] sub33 (input logic [31:0] a,b);
    sub33 = {1'b0,a} - {1'b0,b};
  endfunction

  logic [32:0] sum, diff;
  always_comb begin
    sum  = add33(A,B);
    diff = sub33(A,B);
  end

  // Flag sanity
  assert property (@comb_ev ZF == (F == 32'd0));
  assert property (@comb_ev !$isunknown({F,ZF,OF}));

  // Op-specific behavior
  assert property (@comb_ev (ALU_OP==3'd0) |-> (F==(A&B)       && OF==0));
  assert property (@comb_ev (ALU_OP==3'd1) |-> (F==(A|B)       && OF==0));
  assert property (@comb_ev (ALU_OP==3'd2) |-> (F==(A^B)       && OF==0));
  assert property (@comb_ev (ALU_OP==3'd3) |-> (F==~(A|B)      && OF==0));
  assert property (@comb_ev (ALU_OP==3'd4) |-> (F==sum[31:0]   && OF==(A[31]^B[31]^F[31]^sum[32])));
  assert property (@comb_ev (ALU_OP==3'd5) |-> (F==diff[31:0]  && OF==(A[31]^B[31]^F[31]^diff[32])));
  assert property (@comb_ev (ALU_OP==3'd6) |-> (F==((A<B)?32'd1:32'd0) && OF==0));
  assert property (@comb_ev (ALU_OP==3'd7) |-> (F==(B<<A)      && OF==0));

  // Basic op coverage
  cover property (@comb_ev ALU_OP==3'd0);
  cover property (@comb_ev ALU_OP==3'd1);
  cover property (@comb_ev ALU_OP==3'd2);
  cover property (@comb_ev ALU_OP==3'd3);
  cover property (@comb_ev ALU_OP==3'd4);
  cover property (@comb_ev ALU_OP==3'd5);
  cover property (@comb_ev ALU_OP==3'd6);
  cover property (@comb_ev ALU_OP==3'd7);

  // Flag coverage
  cover property (@comb_ev (ALU_OP inside {3'd4,3'd5}) && OF);
  cover property (@comb_ev ZF);
  cover property (@comb_ev (ALU_OP==3'd7) && (A>31));
endmodule

// ---------- MAIN checker ----------
module MAIN_sva (
  input  logic [2:0]  AB_SW,
  input  logic [2:0]  F_LED_SW,
  input  logic [31:0] A, B, F,
  input  logic        ZF, OF,
  input  logic [7:0]  LED
);
  event comb_ev;  always @* -> comb_ev;

  // A/B selection map
  assert property (@comb_ev (AB_SW==3'b000) |-> (A==32'h0000_0000 && B==32'h0000_0000));
  assert property (@comb_ev (AB_SW==3'b001) |-> (A==32'h0000_0003 && B==32'h0000_0607));
  assert property (@comb_ev (AB_SW==3'b010) |-> (A==32'h8000_0000 && B==32'h8000_0000));
  assert property (@comb_ev (AB_SW==3'b011) |-> (A==32'h7FFF_FFFF && B==32'h7FFF_FFFF));
  assert property (@comb_ev (AB_SW==3'b100) |-> (A==32'hFFFF_FFFF && B==32'hFFFF_FFFF));
  assert property (@comb_ev (AB_SW==3'b101) |-> (A==32'h8000_0000 && B==32'hFFFF_FFFF));
  assert property (@comb_ev (AB_SW==3'b110) |-> (A==32'hFFFF_FFFF && B==32'h8000_0000));
  assert property (@comb_ev (AB_SW==3'b111) |-> (A==32'h1234_5678 && B==32'h3333_2222));

  // LED muxing
  assert property (@comb_ev (F_LED_SW==3'b000) |-> (LED==F[7:0]));
  assert property (@comb_ev (F_LED_SW==3'b001) |-> (LED==F[15:8]));
  assert property (@comb_ev (F_LED_SW==3'b010) |-> (LED==F[23:16]));
  assert property (@comb_ev (F_LED_SW==3'b011) |-> (LED==F[31:24]));
  assert property (@comb_ev !(F_LED_SW inside {3'b000,3'b001,3'b010,3'b011})
                              |-> (LED[7]==ZF && LED[0]==OF && LED[6:1]==6'b0));

  // X/Z on LED
  assert property (@comb_ev !$isunknown(LED));

  // Coverage of inputs and LED default path
  cover property (@comb_ev AB_SW==3'b000);
  cover property (@comb_ev AB_SW==3'b001);
  cover property (@comb_ev AB_SW==3'b010);
  cover property (@comb_ev AB_SW==3'b011);
  cover property (@comb_ev AB_SW==3'b100);
  cover property (@comb_ev AB_SW==3'b101);
  cover property (@comb_ev AB_SW==3'b110);
  cover property (@comb_ev AB_SW==3'b111);

  cover property (@comb_ev F_LED_SW==3'b000);
  cover property (@comb_ev F_LED_SW==3'b001);
  cover property (@comb_ev F_LED_SW==3'b010);
  cover property (@comb_ev F_LED_SW==3'b011);
  cover property (@comb_ev !(F_LED_SW inside {3'b000,3'b001,3'b010,3'b011}) && (ZF||OF));
endmodule

// ---------- Binds ----------
bind ALU  ALU_sva  u_alu_sva  (.A(A), .B(B), .ALU_OP(ALU_OP), .F(F), .ZF(ZF), .OF(OF));
bind MAIN MAIN_sva u_main_sva (.AB_SW(AB_SW), .F_LED_SW(F_LED_SW),
                               .A(A), .B(B), .F(F), .ZF(ZF), .OF(OF), .LED(LED));