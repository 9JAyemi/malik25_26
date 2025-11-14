// SVA checker for priority_encoder (combinational, n must be 4 and m must be 2)
module priority_encoder_sva #(parameter int n=4, m=2) (
  input logic [n-1:0] in,
  input logic [m-1:0] out
);

  // Parameter sanity (the DUT implementation is hard-coded for 4/2)
  initial begin
    assert (n==4 && m==2)
      else $fatal(1, "priority_encoder expects n=4,m=2; got n=%0d,m=%0d", n, m);
  end

  // Combinational functional check + coverage
  always_comb begin
    logic [m-1:0] exp;
    unique case (in)
      4'b1110: exp = 2'b00;
      4'b1101: exp = 2'b01;
      4'b1011: exp = 2'b10;
      4'b0111: exp = 2'b11;
      default: exp = 2'b00;
    endcase

    // No X/Z on output
    assert (!$isunknown(out))
      else $error("priority_encoder: out has X/Z for in=%b", in);

    // Exact functional match
    assert (out === exp)
      else $error("priority_encoder: out mismatch. in=%b out=%b exp=%b", in, out, exp);

    // Functional coverage of each coded case
    cover (in==4'b1110 && out==2'b00);
    cover (in==4'b1101 && out==2'b01);
    cover (in==4'b1011 && out==2'b10);
    cover (in==4'b0111 && out==2'b11);

    // Coverage of default path
    cover (!(in inside {4'b1110,4'b1101,4'b1011,4'b0111}) && out==2'b00);
  end

endmodule

// Bind into the DUT
bind priority_encoder priority_encoder_sva #(.n(n), .m(m)) u_priority_encoder_sva (.in(in), .out(out));