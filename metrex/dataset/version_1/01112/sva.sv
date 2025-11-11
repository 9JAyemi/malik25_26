// SVA binders for the design

module and_module_sva(input logic [3:0] a, b, input logic [3:0] out);
  always_comb begin
    assert (out == (a & b))
      else $error("and_module: out != a & b (a=%b b=%b out=%b)", a, b, out);
    for (int i=0; i<4; i++) begin
      cover ({a[i],b[i]} == 2'b00);
      cover ({a[i],b[i]} == 2'b01);
      cover ({a[i],b[i]} == 2'b10);
      cover ({a[i],b[i]} == 2'b11);
    end
  end
endmodule

module decoder_module_sva(input logic [1:0] sel, input logic [3:0] out);
  always_comb begin
    assert ($onehot(~out))
      else $error("decoder_module: out not one-hot-low: %b", out);
    assert (!(sel==2'b00) || (out==4'b1110))
      else $error("decoder_module: sel=00 wrong out=%b", out);
    assert (!(sel==2'b01) || (out==4'b1101))
      else $error("decoder_module: sel=01 wrong out=%b", out);
    assert (!(sel==2'b10) || (out==4'b1011))
      else $error("decoder_module: sel=10 wrong out=%b", out);
    assert (!(sel==2'b11) || (out==4'b0111))
      else $error("decoder_module: sel=11 wrong out=%b", out);
    cover (sel==2'b00);
    cover (sel==2'b01);
    cover (sel==2'b10);
    cover (sel==2'b11);
    cover (out==4'b1110);
    cover (out==4'b1101);
    cover (out==4'b1011);
    cover (out==4'b0111);
  end
endmodule

module mux_module_sva(
  input logic [3:0] a, b,
  input logic       A, B,
  input logic       out,
  input logic [3:0] and_out,
  input logic [3:0] decoder_out
);
  logic [1:0] sel = {A,B};
  always_comb begin
    // End-to-end mux check
    assert (out == (a & b)[sel])
      else $error("mux_module: out != (a&b)[sel] (a=%b b=%b sel=%b out=%0b)", a, b, sel, out);
    // Decoder integrity in-context
    assert ($onehot(~decoder_out))
      else $error("mux_module: decoder_out not one-hot-low: %b", decoder_out);
    assert (!(sel==2'b00) || (decoder_out==4'b1110));
    assert (!(sel==2'b01) || (decoder_out==4'b1101));
    assert (!(sel==2'b10) || (decoder_out==4'b1011));
    assert (!(sel==2'b11) || (decoder_out==4'b0111));
    // Selection consistency with internal signals
    assert (out == |(and_out & ~decoder_out))
      else $error("mux_module: out != |(and_out & ~decoder_out)");
    // Coverage of each select path
    cover (sel==2'b00 && out == (a[0] & b[0]));
    cover (sel==2'b01 && out == (a[1] & b[1]));
    cover (sel==2'b10 && out == (a[2] & b[2]));
    cover (sel==2'b11 && out == (a[3] & b[3]));
  end
endmodule

module top_module_sva(
  input logic [3:0] a, b,
  input logic       A, B,
  input logic       out
);
  logic [1:0] sel = {A,B};
  always_comb begin
    assert (out == ~((a & b)[sel]))
      else $error("top_module: out != ~((a&b)[sel]) (a=%b b=%b sel=%b out=%0b)", a, b, sel, out);
    cover (out==1'b0);
    cover (out==1'b1);
  end
endmodule

// Bindings
bind and_module     and_module_sva     u_and_module_sva     (.*);
bind decoder_module decoder_module_sva u_decoder_module_sva (.*);
bind mux_module     mux_module_sva     u_mux_module_sva     (.*);
bind top_module     top_module_sva     u_top_module_sva     (.*);