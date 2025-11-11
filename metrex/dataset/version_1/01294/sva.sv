// SVA for alu4bit
// Bind-time inputs clk/rst_n are assumed to exist in the testbench/top.
// Adjust names in the bind line if needed.

module alu4bit_sva (
  input logic        clk,
  input logic        rst_n,
  input logic [3:0]  A, B,
  input logic        CIN, BINV,
  input logic [1:0]  OP,
  input logic        COUT,
  input logic [3:0]  Y
);
  // Pure combinational specs
  wire [3:0] B_eff = BINV ? ~B : B;
  wire [4:0] ADD5  = A + B_eff + CIN;
  wire [4:0] SUB5  = A - B_eff - ~CIN;

  // Functional correctness per OP
  ap_add: assert property (@(posedge clk) disable iff (!rst_n)
    (OP==2'b00) |-> ({COUT,Y} == ADD5)
  );

  ap_sub: assert property (@(posedge clk) disable iff (!rst_n)
    (OP==2'b01) |-> ({COUT,Y} == SUB5)
  );

  ap_and: assert property (@(posedge clk) disable iff (!rst_n)
    (OP==2'b10) |-> (Y == (A & B_eff) && COUT==1'b0)
  );

  ap_or: assert property (@(posedge clk) disable iff (!rst_n)
    (OP==2'b11) |-> (Y == (A | B_eff) && COUT==1'b0)
  );

  // X-prop hygiene: known inputs imply known outputs
  ap_known: assert property (@(posedge clk) disable iff (!rst_n)
    !$isunknown({A,B,CIN,BINV,OP}) |-> !$isunknown({COUT,Y})
  );

  // Minimal but meaningful functional coverage
  // Exercise all OP values, BINV and CIN where relevant, and COUT polarity on arithmetic
  cp_op00_binvcin: cover property (@(posedge clk) OP==2'b00 && !BINV && !CIN);
  cp_op00_binv:    cover property (@(posedge clk) OP==2'b00 &&  BINV &&  CIN);
  cp_op00_cout0:   cover property (@(posedge clk) OP==2'b00 && COUT==0);
  cp_op00_cout1:   cover property (@(posedge clk) OP==2'b00 && COUT==1);

  cp_op01_binvcin: cover property (@(posedge clk) OP==2'b01 && !BINV && !CIN);
  cp_op01_binv:    cover property (@(posedge clk) OP==2'b01 &&  BINV &&  CIN);
  cp_op01_cout0:   cover property (@(posedge clk) OP==2'b01 && COUT==0);
  cp_op01_cout1:   cover property (@(posedge clk) OP==2'b01 && COUT==1);

  cp_op10_binv0:   cover property (@(posedge clk) OP==2'b10 && !BINV);
  cp_op10_binv1:   cover property (@(posedge clk) OP==2'b10 &&  BINV);
  cp_and_zero:     cover property (@(posedge clk) OP==2'b10 && Y==4'h0);

  cp_op11_binv0:   cover property (@(posedge clk) OP==2'b11 && !BINV);
  cp_op11_binv1:   cover property (@(posedge clk) OP==2'b11 &&  BINV);
  cp_or_all1:      cover property (@(posedge clk) OP==2'b11 && Y==4'hF);
endmodule

// Bind to DUT instance(s). Replace clk/rst_n with your TB signals if different.
bind alu4bit alu4bit_sva u_alu4bit_sva (
  .clk   (clk),
  .rst_n (rst_n),
  .A     (A),
  .B     (B),
  .CIN   (CIN),
  .BINV  (BINV),
  .OP    (OP),
  .COUT  (COUT),
  .Y     (Y)
);