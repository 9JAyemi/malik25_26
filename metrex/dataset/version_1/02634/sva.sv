// SVA for alupipe and sub-blocks (concise, quality-focused)
// Bind this file alongside the DUT

// -------------------- DFF checker --------------------
module sva_dff #(parameter W=32) (input logic clk,
                                  input logic [W-1:0] dataIn,
                                  input logic [W-1:0] dataOut);
  default clocking @(posedge clk); endclocking
  logic started; initial started = 1'b0; always @(posedge clk) started = 1'b1;

  // Edge-transfer check
  ap_dff_xfer: assert property (started |-> dataOut == $past(dataIn));
endmodule

bind DflipFlop sva_dff #(.W(32))) dff_chk (.clk(clk), .dataIn(dataIn), .dataOut(dataOut));


// -------------------- alu_cell checker (bit-accurate) --------------------
module sva_alu_cell (input logic a, b, c,
                     input logic [2:0] S,
                     input logic p, g, d);
  // Combinational immediate assertions
  always @* begin
    // p/g definitions
    assert (p == (a ^ (b ^ S[0])));
    assert (g == (a & (b ^ S[0])));

    // d selection
    if (!S[2]) begin
      assert (d == (p ^ (S[1] & c)));
    end else begin
      unique case (S[1:0])
        2'b00: assert (d == (a | b));
        2'b01: assert (d == ~(a | b));
        2'b10: assert (d == (a & b));
        2'b11: assert (d == 1'b1);
      endcase
    end
  end
endmodule

bind alu_cell sva_alu_cell cell_chk (.a(a), .b(b), .c(c), .S(S), .p(p), .g(g), .d(d));


// -------------------- alu32 checker (vector-level: carries, d, gout/pout, Cout/V) --------------------
module sva_alu32 (input  logic [31:0] a, b,
                  input  logic        Cin,
                  input  logic [2:0]  S,
                  input  logic [31:0] d, g, p, c,
                  input  logic        gout, pout,
                  input  logic        Cout, V);

  // Helpers
  function automatic [31:0] calc_carry_vec (input logic [31:0] g_i,
                                            input logic [31:0] p_i,
                                            input logic        Cin_i);
    automatic logic [31:0] c_o;
    int i;
    c_o[0] = Cin_i;
    for (i = 1; i < 32; i++) begin
      c_o[i] = g_i[i-1] | (p_i[i-1] & c_o[i-1]);
    end
    return c_o;
  endfunction

  function automatic logic group_generate (input logic [31:0] g_i,
                                           input logic [31:0] p_i,
                                           input int          idx);
    if (idx == 0) return g_i[0];
    else          return g_i[idx] | (p_i[idx] & group_generate(g_i, p_i, idx-1));
  endfunction

  // Combinational reference
  logic [31:0] b_xor, p_exp, g_exp, c_exp, d_add_exp, d_logic_exp, d_exp;
  logic gout_exp, pout_exp, Cout_exp;

  always @* begin
    b_xor      = b ^ {32{S[0]}};
    p_exp      = a ^ b_xor;
    g_exp      = a & b_xor;
    c_exp      = calc_carry_vec(g_exp, p_exp, Cin);
    pout_exp   = &p_exp;
    gout_exp   = group_generate(g_exp, p_exp, 31);
    d_add_exp  = p_exp ^ ({32{S[1]}} & c_exp);
    case (S[1:0])
      2'b00: d_logic_exp = (a | b);
      2'b01: d_logic_exp = ~(a | b);
      2'b10: d_logic_exp = (a & b);
      default: d_logic_exp = {32{1'b1}};
    endcase
    d_exp      = (S[2] == 1'b0) ? d_add_exp : d_logic_exp;
    Cout_exp   = gout_exp | (pout_exp & Cin);

    // Carries from LAC must match reference from a,b,S
    assert (c == c_exp);

    // Group propagate/generate
    assert (pout == pout_exp);
    assert (gout == gout_exp);

    // Result
    assert (d == d_exp);

    // Overflow stage consistency
    assert (Cout == Cout_exp);
    assert (V == (Cout ^ c[31]));
  end
endmodule

bind alu32 sva_alu32 alu32_chk (
  .a(a), .b(b), .Cin(Cin), .S(S),
  .d(d), .g(g), .p(p), .c(c),
  .gout(gout), .pout(pout),
  .Cout(Cout), .V(V)
);


// -------------------- overflow checker (local equivalence) --------------------
module sva_overflow (input logic g, p, c31, Cin,
                     input logic Cout, V);
  always @* begin
    assert (Cout == (g | (p & Cin)));
    assert (V    == (Cout ^ c31));
  end
endmodule

bind overflow sva_overflow ovf_chk (.g(g), .p(p), .c31(c31), .Cin(Cin), .Cout(Cout), .V(V));


// -------------------- Top alupipe pipeline checks + coverage --------------------
module sva_alupipe (input logic        clk,
                    input logic [31:0] abus, bbus, dbus,
                    input logic [2:0]  S,
                    input logic        Cin,
                    input logic [31:0] aInput, bInput, dInput,
                    input logic        ALU_V, ALU_Cout, ALU_gout, ALU_pout);

  default clocking @(posedge clk); endclocking
  logic started; initial started = 1'b0; always @(posedge clk) started = 1'b1;

  // Pipeline register checks
  ap_pipe_a: assert property (started |-> aInput == $past(abus));
  ap_pipe_b: assert property (started |-> bInput == $past(bbus));
  ap_pipe_d: assert property (started |-> dbus  == $past(dInput));

  // Lightweight functional coverage
  // Cover all opcodes
  cover property (S == 3'b000);
  cover property (S == 3'b001);
  cover property (S == 3'b010);
  cover property (S == 3'b011);
  cover property (S == 3'b100);
  cover property (S == 3'b101);
  cover property (S == 3'b110);
  cover property (S == 3'b111);

  // Arithmetic carry-in toggles
  cover property (!S[2] && (Cin == 1'b0));
  cover property (!S[2] && (Cin == 1'b1));

  // Group propagate/generate extremes and overflow occurrence
  cover property (ALU_pout);      // full propagate
  cover property (ALU_gout);      // group generate asserted
  cover property (ALU_V);         // overflow observed
endmodule

bind alupipe sva_alupipe pipe_chk (
  .clk(clk), .abus(abus), .bbus(bbus), .dbus(dbus), .S(S), .Cin(Cin),
  .aInput(aInput), .bInput(bInput), .dInput(dInput),
  .ALU_V(ALU.V), .ALU_Cout(ALU.Cout), .ALU_gout(ALU.gout), .ALU_pout(ALU.pout)
);