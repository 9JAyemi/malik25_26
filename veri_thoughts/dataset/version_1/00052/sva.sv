// SVA for nand_gate and decoder_2to4 (bind-only, concise, full functional checks + coverage)

module nand_gate_sva(input logic a, b, y);
  // Functional check (skip when inputs unknown)
  always_comb begin
    if (!$isunknown({a,b})) begin
      assert (y === ~(a & b)) else
        $error("nand_gate: y != ~(a & b): a=%b b=%b y=%b", a,b,y);
      assert (!$isunknown(y)) else
        $error("nand_gate: y is X/Z with known inputs: a=%b b=%b y=%b", a,b,y);
    end
    // Coverage (truth table)
    cover ({a,b,y} === 3'b001);
    cover ({a,b,y} === 3'b011);
    cover ({a,b,y} === 3'b101);
    cover ({a,b,y} === 3'b110);
  end
endmodule

bind nand_gate nand_gate_sva u_nand_gate_sva(.a(a), .b(b), .y(y));


module decoder_2to4_sva(
  input  logic [1:0] in,
  input  logic [3:0] out,
  // tap internal nets
  input  logic       n1, n2
);
  // Internal wiring checks to spec (helpful root-cause on failures)
  always_comb begin
    if (!$isunknown(in)) begin
      assert (n1 === ~(in[0] & in[1])) else
        $error("decoder: n1 wrong: in=%b n1=%b", in, n1);
      assert (n2 === ~(in[0] & ~in[1])) else
        $error("decoder: n2 wrong: in=%b n2=%b", in, n2);
    end
  end

  // Functional decode: exact 1-hot equals 1 << in
  always_comb begin
    if (!$isunknown(in)) begin
      assert (out === (4'b0001 << in)) else
        $error("decoder: out != (1<<in): in=%b out=%b", in, out);
      assert ($onehot(out)) else
        $error("decoder: out not one-hot: in=%b out=%b", in, out);
      assert (!$isunknown(out)) else
        $error("decoder: out has X/Z with known in: in=%b out=%b", in, out);
    end
  end

  // Bitwise mapping cross-checks (redundant but pinpoint which bit fails)
  always_comb begin
    if (!$isunknown(in)) begin
      assert (out[0] === (in == 2'b00));
      assert (out[1] === (in == 2'b01));
      assert (out[2] === (in == 2'b10));
      assert (out[3] === (in == 2'b11));
    end
  end

  // Coverage: hit all input codes and corresponding outputs
  always_comb begin
    cover (! $isunknown(in) && in==2'b00 && out==4'b0001);
    cover (! $isunknown(in) && in==2'b01 && out==4'b0010);
    cover (! $isunknown(in) && in==2'b10 && out==4'b0100);
    cover (! $isunknown(in) && in==2'b11 && out==4'b1000);
  end
endmodule

bind decoder_2to4 decoder_2to4_sva u_decoder_2to4_sva(
  .in(in), .out(out), .n1(n1), .n2(n2)
);