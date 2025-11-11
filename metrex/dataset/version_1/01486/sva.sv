// SVA checkers and binds for top_module and carry_lookahead_adder

// Checker bound into carry_lookahead_adder.
// Uses the instance scope to access internal p0..p7 and g0..g7 wires.
module cla_sva;

  // Expected carry chain (g vector) and sum (p/s) given a,b,c_in
  function automatic logic [7:0] exp_g(input logic [7:0] a, b, input logic c_in);
    logic [7:0] cvec;
    logic carry;
    int i;
    carry = c_in;
    for (i=0;i<8;i++) begin
      cvec[i] = (a[i] & b[i]) | (carry & (a[i] ^ b[i]));
      carry   = cvec[i];
    end
    return cvec;
  endfunction

  function automatic logic [7:0] exp_s(input logic [7:0] a, b, input logic c_in);
    logic [7:0] sum;
    logic carry;
    int i;
    carry = c_in;
    for (i=0;i<8;i++) begin
      sum[i]  = a[i] ^ b[i] ^ carry;
      carry   = (a[i] & b[i]) | (carry & (a[i] ^ b[i]));
    end
    return sum;
  endfunction

  wire inputs_known = !$isunknown({a,b,c_in});

  // Environment assumption (matches top: c_in is tied low)
  assume property (@*) c_in == 1'b0;

  // Internal carry chain and sum equations must match arithmetic
  assert property (@*) inputs_known |-> {g7,g6,g5,g4,g3,g2,g1,g0} == exp_g(a,b,c_in);
  assert property (@*) inputs_known |-> {p7,p6,p5,p4,p3,p2,p1,p0} == exp_s(a,b,c_in);

  // Output buses must match internal vectors
  assert property (@*) inputs_known |-> s == {p7,p6,p5,p4,p3,p2,p1,p0};
  assert property (@*) inputs_known |-> c == {g7,g6,g5,g4,g3,g2,g1,g0};
  assert property (@*) inputs_known |-> p == {p7,p6,p5,p4,p3,p2,p1,p0};

  // Catch width/mapping issues on g output (intended: pass out g7..g0)
  assert property (@*) inputs_known |-> g == {g7,g6,g5,g4,g3,g2,g1,g0};

  // No X/Z on outputs when inputs are known
  assert property (@*) inputs_known |-> !$isunknown({s,c,p,g,{g7,g6,g5,g4,g3,g2,g1,g0},{p7,p6,p5,p4,p3,p2,p1,p0}});

  // Basic carry-out coverage
  cover property (@*) inputs_known && exp_g(a,b,1'b0)[7] == 1'b0;
  cover property (@*) inputs_known && exp_g(a,b,1'b0)[7] == 1'b1;

endmodule

bind carry_lookahead_adder cla_sva cla_sva_i();

// Checker bound into top_module for end-to-end properties and overflow
module top_sva;

  wire inputs_known = !$isunknown({a,b});

  // Adder must be tied with c_in=0
  assert property (@*) adder.c_in == 1'b0;

  // Sum correctness (mod 2^8)
  assert property (@*) inputs_known |-> s == (a + b)[7:0];

  // Signed overflow correctness
  assert property (@*) inputs_known |-> overflow == ((a[7] == b[7]) && (a[7] != s[7]));

  // Cross-check overflow via carry into/out of MSB: overflow == c6 ^ c7
  assert property (@*) inputs_known |-> overflow == (c_out[7] ^ c_out[6]);

  // No X/Z on outputs when inputs known
  assert property (@*) inputs_known |-> !$isunknown({s,overflow});

  // Coverage: overflow and non-overflow, key signed cases, carry-out without overflow
  cover property (@*) inputs_known && overflow;
  cover property (@*) inputs_known && !overflow;
  cover property (@*) inputs_known && (a[7]==0) && (b[7]==0) && (s[7]==1); // + + -> -
  cover property (@*) inputs_known && (a[7]==1) && (b[7]==1) && (s[7]==0); // - - -> +
  cover property (@*) inputs_known && (c_out[7]==1) && !overflow;          // carry-out w/o signed overflow

endmodule

bind top_module top_sva top_sva_i();