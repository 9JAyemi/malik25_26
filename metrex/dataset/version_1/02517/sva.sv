// SVA checker for shipping_module
// Bind this to your DUT and provide clk/rst_n from your TB/environment.

module shipping_module_sva (
  input logic clk,
  input logic rst_n,
  input logic A,B,C,D,E,F,G,H,I,J,K,L,M,N,
  input logic valid
);

  // Default clock
  default clocking cb @(posedge clk); endclocking

  // 8-bit truncated totals (match DUT semantics)
  function automatic logic [7:0] value8
    (input logic A,B,C,D,E,F,G,H,I,J,K,L,M,N);
    int unsigned s;
    begin
      s =   A*4  + B*8  + C*0  + D*20 + E*10 + F*12 + G*18
          + H*14 + I*6  + J*15 + K*30 + L*8  + M*16 + N*18;
      return s[7:0];
    end
  endfunction

  function automatic logic [7:0] weight8
    (input logic A,B,C,D,E,F,G,H,I,J,K,L,M,N);
    int unsigned s;
    begin
      s =   A*28 + B*8  + C*27 + D*18 + E*27 + F*28 + G*6
          + H*1  + I*20 + J*0  + K*5  + L*13 + M*8  + N*14;
      return s[7:0];
    end
  endfunction

  function automatic logic [7:0] volume8
    (input logic A,B,C,D,E,F,G,H,I,J,K,L,M,N);
    int unsigned s;
    begin
      s =   A*27 + B*27 + C*4  + D*4  + E*0  + F*24 + G*4
          + H*20 + I*12 + J*15 + K*5  + L*2  + M*9  + N*28;
      return s[7:0];
    end
  endfunction

  function automatic logic valid_exp
    (input logic A,B,C,D,E,F,G,H,I,J,K,L,M,N);
    logic [7:0] v,w,u;
    begin
      v = value8(A,B,C,D,E,F,G,H,I,J,K,L,M,N);
      w = weight8(A,B,C,D,E,F,G,H,I,J,K,L,M,N);
      u = volume8(A,B,C,D,E,F,G,H,I,J,K,L,M,N);
      return (v >= 8'd120) && (w <= 8'd60) && (u <= 8'd60);
    end
  endfunction

  // Wide totals for overflow coverage
  function automatic int unsigned valueW
    (input logic A,B,C,D,E,F,G,H,I,J,K,L,M,N);
    return   A*4  + B*8  + C*0  + D*20 + E*10 + F*12 + G*18
           + H*14 + I*6  + J*15 + K*30 + L*8  + M*16 + N*18;
  endfunction
  function automatic int unsigned weightW
    (input logic A,B,C,D,E,F,G,H,I,J,K,L,M,N);
    return   A*28 + B*8  + C*27 + D*18 + E*27 + F*28 + G*6
           + H*1  + I*20 + J*0  + K*5  + L*13 + M*8  + N*14;
  endfunction
  function automatic int unsigned volumeW
    (input logic A,B,C,D,E,F,G,H,I,J,K,L,M,N);
    return   A*27 + B*27 + C*4  + D*4  + E*0  + F*24 + G*4
           + H*20 + I*12 + J*15 + K*5  + L*2  + M*9  + N*28;
  endfunction

  // Knownness
  assert property (disable iff (!rst_n)
    !$isunknown({A,B,C,D,E,F,G,H,I,J,K,L,M,N,valid})
  ) else $error("shipping_module: X/Z detected on inputs or valid");

  // Combinational equivalence: valid must match spec
  assert property (disable iff (!rst_n)
    valid === valid_exp(A,B,C,D,E,F,G,H,I,J,K,L,M,N)
  ) else $error("shipping_module: valid mismatch");

  // Stability: if inputs hold, valid holds
  assert property (disable iff (!rst_n)
    $stable({A,B,C,D,E,F,G,H,I,J,K,L,M,N}) |-> $stable(valid)
  ) else $error("shipping_module: valid changed without input change");

  // Sanity: with no items selected, must be invalid
  assert property (disable iff (!rst_n)
    ({A,B,C,D,E,F,G,H,I,J,K,L,M,N} == '0) |-> (valid == 1'b0)
  ) else $error("shipping_module: empty selection should be invalid");

  // Coverage
  cover property (disable iff (!rst_n) valid);
  cover property (disable iff (!rst_n) !valid);

  // Boundary coverage at thresholds (using truncated totals)
  cover property (disable iff (!rst_n)
    value8(A,B,C,D,E,F,G,H,I,J,K,L,M,N) == 8'd120
      && weight8(A,B,C,D,E,F,G,H,I,J,K,L,M,N) <= 8'd60
      && volume8(A,B,C,D,E,F,G,H,I,J,K,L,M,N) <= 8'd60
  );
  cover property (disable iff (!rst_n)
    weight8(A,B,C,D,E,F,G,H,I,J,K,L,M,N) == 8'd60
  );
  cover property (disable iff (!rst_n)
    volume8(A,B,C,D,E,F,G,H,I,J,K,L,M,N) == 8'd60
  );

  // Exercise single-selection scenario
  cover property (disable iff (!rst_n) $onehot({A,B,C,D,E,F,G,H,I,J,K,L,M,N}));

  // Overflow coverage (detect when wide sum exceeds 8 bits)
  cover property (disable iff (!rst_n) valueW(A,B,C,D,E,F,G,H,I,J,K,L,M,N) > 255);
  cover property (disable iff (!rst_n) weightW(A,B,C,D,E,F,G,H,I,J,K,L,M,N) > 255);
  cover property (disable iff (!rst_n) volumeW(A,B,C,D,E,F,G,H,I,J,K,L,M,N) > 255);

endmodule

// Example bind (hook clk/rst_n from your TB):
// bind shipping_module shipping_module_sva u_sva ( .clk(clk), .rst_n(rst_n),
//   .A(A),.B(B),.C(C),.D(D),.E(E),.F(F),.G(G),.H(H),.I(I),.J(J),.K(K),.L(L),.M(M),.N(N),
//   .valid(valid) );