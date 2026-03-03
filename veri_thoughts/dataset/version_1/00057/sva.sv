// SVA for adder_4bit and full_adder
// Focus: correctness, X-propagation, and concise yet meaningful coverage.

module adder_4bit_sva(
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic       reset,
  input  logic [3:0] S,
  input  logic [3:0] carry,
  input  logic [3:0] sum
);

  // Combinational correctness and X checks
  always_comb begin
    automatic logic [4:0] expected = A + B + reset;

    assert (S == expected[3:0])
      else $error("adder_4bit S mismatch: A=%0h B=%0h cin=%0b S=%0h exp=%0h",
                  A, B, reset, S, expected[3:0]);

    assert (carry[3] == expected[4])
      else $error("adder_4bit final carry mismatch: A=%0h B=%0h cin=%0b c3=%0b exp_c3=%0b",
                  A, B, reset, carry[3], expected[4]);

    // Bitwise ripple, propagate/generate checks
    automatic logic prev_c = reset;
    for (int i = 0; i < 4; i++) begin
      automatic logic P = A[i] ^ B[i];
      automatic logic G = A[i] & B[i];

      assert (sum[i] == (P ^ prev_c))
        else $error("sum[%0d] mismatch: Ai=%0b Bi=%0b Cin=%0b sum=%0b exp=%0b",
                    i, A[i], B[i], prev_c, sum[i], (P ^ prev_c));

      assert (carry[i] == (G | (P & prev_c)))
        else $error("carry[%0d] mismatch: Ai=%0b Bi=%0b Cin=%0b cout=%0b exp=%0b",
                    i, A[i], B[i], prev_c, carry[i], (G | (P & prev_c)));

      prev_c = carry[i];
    end

    if (!$isunknown({A,B,reset})) begin
      assert (!$isunknown({S,carry,sum}))
        else $error("X/Z on outputs with known inputs: A=%0h B=%0h cin=%0b S=%0h carry=%0h sum=%0h",
                    A, B, reset, S, carry, sum);
    end
  end

  // Concise functional coverage
  // - All S values (0..15)
  // - cin (reset) toggling
  // - overflow (final carry) observed
  covergroup cg_adder @(posedge $sampled_event);
    coverpoint reset { bins zero = {0}; bins one = {1}; }
    coverpoint S     { bins all[] = {[0:15]}; }
    coverpoint carry3 = carry[3] { bins zero = {0}; bins one = {1}; }
    cross reset, carry3;
  endgroup
  cg_adder cga = new;

  // Simple event to sample on any input change (tool-friendly)
  event $sampled_event;
  always_comb -> $sampled_event;
  always_comb cga.sample();

endmodule


module full_adder_sva(
  input  logic a,
  input  logic b,
  input  logic cin,
  input  logic sum,
  input  logic cout
);

  // Combinational correctness and X checks
  always_comb begin
    assert (sum  == (a ^ b ^ cin))
      else $error("FA sum mismatch: a=%0b b=%0b cin=%0b sum=%0b exp=%0b",
                  a, b, cin, sum, (a ^ b ^ cin));

    assert (cout == ((a & b) | (a & cin) | (b & cin)))
      else $error("FA cout mismatch: a=%0b b=%0b cin=%0b cout=%0b exp=%0b",
                  a, b, cin, cout, ((a & b) | (a & cin) | (b & cin)));

    if (!$isunknown({a,b,cin})) begin
      assert (!$isunknown({sum,cout}))
        else $error("FA X/Z on outputs with known inputs: a=%0b b=%0b cin=%0b sum=%0b cout=%0b",
                    a, b, cin, sum, cout);
    end
  end

  // Full truth-table coverage in one compact covergroup
  covergroup cg_fa @(posedge $sampled_event);
    coverpoint {a,b,cin}  { bins all[] = {[0:7]}; }
    coverpoint {sum,cout} { bins all[] = {[0:3]}; }
    cross {a,b,cin}, {sum,cout};
  endgroup
  cg_fa cgf = new;

  event $sampled_event;
  always_comb -> $sampled_event;
  always_comb cgf.sample();

endmodule


// Bind SVA to DUTs (grants access to internal sum/carry in adder_4bit)
bind adder_4bit  adder_4bit_sva u_adder_4bit_sva(.A(A), .B(B), .reset(reset), .S(S), .carry(carry), .sum(sum));
bind full_adder  full_adder_sva u_full_adder_sva(.a(a), .b(b), .cin(cin), .sum(sum), .cout(cout));