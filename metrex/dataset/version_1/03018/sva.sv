// SVA checker for sig_337p
module sig_337p_sva(input logic [6:0] t, input logic [7:0] y);

  // reference recompute (from t only)
  logic [6:0]  temp;
  logic [26:0] p;
  logic [7:0]  s, y_ref;

  always_comb begin
    temp = t[6] ? (~t + 1'b1) : t;

    p[0]  =  temp[5] &  temp[2];
    p[1]  =  temp[5] &  temp[4];
    p[2]  =  temp[5];
    p[3]  =  temp[5] &  temp[3];
    p[4]  =  temp[4] & ~temp[3] & ~temp[2] & ~temp[1] & ~temp[0];
    p[5]  = ~temp[4] &  temp[3] & ~temp[2] & ~temp[1] & ~temp[0];
    p[6]  = ~temp[4] & ~temp[3] &  temp[2] &  temp[1] & ~temp[0];
    p[7]  =  temp[3] & ~temp[2] &  temp[1] & ~temp[0];
    p[8]  =  temp[4] &  temp[3] &  temp[1] &  temp[0];
    p[9]  =  temp[4] & ~temp[3] &  temp[1] &  temp[0];
    p[10] =  temp[4] &  temp[2] &  temp[1];
    p[11] = ~temp[4] &  temp[3] &  temp[1] &  temp[0];
    p[12] =  temp[3] &  temp[2] &  temp[1];
    p[13] =  temp[3] & ~temp[1] &  temp[0];
    p[14] =  temp[4] &  temp[2] &  temp[0];
    p[15] =  temp[4] & ~temp[3] & ~temp[2] &  temp[1];
    p[16] = ~temp[4] & ~temp[3] & ~temp[2] &  temp[1];
    p[17] = ~temp[4] &  temp[3] &  temp[2];
    p[18] =  temp[4] &  temp[3] &  temp[2];
    p[19] = ~temp[3] &  temp[2];
    p[20] = ~temp[4] &  temp[2] &  temp[1] &  temp[0];
    p[21] = ~temp[4] &  temp[2] & ~temp[1] &  temp[0];
    p[22] =  temp[4] & ~temp[3] &  temp[2] & ~temp[1];
    p[23] =  temp[4] & ~temp[2] & ~temp[1] &  temp[0];
    p[24] = ~temp[4] & ~temp[3] & ~temp[2] &  temp[0];
    p[25] =  temp[4] &  temp[3];
    p[26] =  temp[4] &  temp[3] & ~temp[2] & ~temp[0];

    s[7] = 1'b0;
    s[6] = 1'b1;
    s[5] = p[2] | p[4] | p[7] | p[9] | p[10] | p[11] | p[12] | p[13] |
           p[14] | p[15] | p[17] | p[22] | p[23] | p[25];
    s[4] = p[2] | p[4] | p[5] | p[9] | p[10] | p[14] | p[15] | p[19] |
           p[23] | p[25];
    s[3] = p[2] | p[5] | p[10] | p[12] | p[16] | p[17] | p[20] | p[25];
    s[2] = p[2] | p[5] | p[6] | p[8] | p[11] | p[12] | p[15] | p[18] |
           p[22] | p[24];
    s[1] = p[2] | p[5] | p[6] | p[7] | p[11] | p[20] | p[21] | p[22] |
           p[23] | p[26];
    s[0] = p[0] | p[1] | p[3] | p[4] | p[6] | p[7] | p[9] | p[12] |
           p[13] | p[14] | p[17] | p[21];

    y_ref = t[6] ? (8'h80 - s) : s;
  end

  // pseudo-clock for concurrent SVA on combinational logic
  logic ev; initial ev = 1'b0;
  always @(t or y) ev <= ~ev;
  default clocking cb @(posedge ev); endclocking

  // Basic correctness
  assert property (!$isunknown(t) && !$isunknown(y));
  assert property (y == y_ref);

  // Structural constraints implied by design
  assert property (s[7] == 1'b0 && s[6] == 1'b1);
  assert property (y[7] == 1'b0);
  assert property ((t[6]==1'b0) |-> (y == s && (y >= 8'd64 && y <= 8'd127)));
  assert property ((t[6]==1'b1) |-> (y == (8'h80 - s) && (y >= 8'd1 && y <= 8'd64)));

  // Functional coverage
  cover property (t[6]==1'b0);
  cover property (t[6]==1'b1);
  cover property (y==8'd64);
  cover property (y==8'd127);
  cover property (y==8'd1);
  // Stimulus corners on t
  cover property (t==7'b0000000);
  cover property (t==7'b0111111);
  cover property (t==7'b1000000);
  cover property (t==7'b1111111);
  // Ensure each primitive term can be exercised
  cover property (p[0]);  cover property (p[1]);  cover property (p[2]);
  cover property (p[3]);  cover property (p[4]);  cover property (p[5]);
  cover property (p[6]);  cover property (p[7]);  cover property (p[8]);
  cover property (p[9]);  cover property (p[10]); cover property (p[11]);
  cover property (p[12]); cover property (p[13]); cover property (p[14]);
  cover property (p[15]); cover property (p[16]); cover property (p[17]);
  cover property (p[18]); cover property (p[19]); cover property (p[20]);
  cover property (p[21]); cover property (p[22]); cover property (p[23]);
  cover property (p[24]); cover property (p[25]); cover property (p[26]);

endmodule

// Bind into the DUT
bind sig_337p sig_337p_sva u_sig_337p_sva(.t(t), .y(y));