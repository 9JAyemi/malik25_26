// SVA checker for adder4
module adder4_sva #(
  parameter bit HAS_CLK = 0
)(
  input logic              clk,       // optional for coverage
  input logic [3:0]        a,
  input logic [3:0]        b,
  input logic              cin,
  input logic [3:0]        sum,
  input logic              cout,
  input logic [3:0]        xor_out,
  input logic [3:0]        and_out,
  input logic [3:0]        or_out
);

  // Combinational correctness and X checks
  always_comb begin
    logic [3:0] p = a ^ b;
    logic [3:0] g = a & b;
    logic       c0 = cin;
    logic       c1 = g[0] | (p[0] & c0);
    logic       c2 = g[1] | (p[1] & c1);
    logic       c3 = g[2] | (p[2] & c2);
    logic       c4 = g[3] | (p[3] & c3);

    assert ({cout, sum} == a + b + cin)
      else $error("adder4: wrong result a=%0h b=%0h cin=%0b -> sum=%0h cout=%0b", a, b, cin, sum, cout);

    assert (xor_out == p)
      else $error("adder4: xor_out mismatch");
    assert (and_out == g)
      else $error("adder4: and_out mismatch");
    assert (or_out  == (a | b))
      else $error("adder4: or_out mismatch");

    assert (sum  == (p ^ {c3,c2,c1,c0}))
      else $error("adder4: sum bits don't match ripple-carry");
    assert (cout == c4)
      else $error("adder4: cout doesn't match carry-lookahead");

    assert (!$isunknown({a,b,cin,sum,cout,xor_out,and_out,or_out}))
      else $error("adder4: X/Z detected on signals");
  end

  // Optional clocked functional coverage (enable by setting HAS_CLK=1 and wiring clk)
  if (HAS_CLK) begin
    default clocking @(posedge clk); endclocking

    // Key scenarios
    cover property (~|a && ~|b && !cin);          // all zeros
    cover property (&a && &b && cin);             // all ones + cin
    cover property (cin && &(a^b) && ~|(a&b));    // full propagate chain with cin=1
    cover property ((a & b)[3]);                  // MSB generate

    // Per-bit generate/propagate/kill and output toggles
    genvar i;
    for (i=0; i<4; i++) begin : g_cov
      cover property ((a[i]&b[i]));                    // generate
      cover property ((a[i]^b[i]));                    // propagate
      cover property (!(a[i]^b[i]) && !(a[i]&b[i]));   // kill (00)
      cover property ($rose(sum[i]));
      cover property ($fell(sum[i]));
    end
    cover property ($rose(cout));
    cover property ($fell(cout));
  end

endmodule

// Bind without clock (assertions only)
bind adder4 adder4_sva #(.HAS_CLK(0)) u_adder4_sva_noclk (
  .clk(), .a(a), .b(b), .cin(cin), .sum(sum), .cout(cout),
  .xor_out(xor_out), .and_out(and_out), .or_out(or_out)
);

// Example bind with clock for coverage (adjust hierarchical clk path as needed)
// bind top.u_adder4_inst adder4_sva #(.HAS_CLK(1)) u_adder4_sva_clk (
//   .clk(top.tb_clk), .a(a), .b(b), .cin(cin), .sum(sum), .cout(cout),
//   .xor_out(xor_out), .and_out(and_out), .or_out(or_out)
// );