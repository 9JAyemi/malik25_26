// SVA for 74x138-style 3-to-8 active-low decoder
// Checks enable behavior, one-hot decode, and full coverage per code point.

module decoder_74138_sva(
  input  logic [2:0] x,
  input  logic       g1, g2a_n, g2b_n,
  input  logic [7:0] y
);

  // Enabled when g1=1 and both g2*_n=0
  logic en;
  assign en = g1 & ~g2a_n & ~g2b_n;

  // Sample on any relevant input edge
  `define DEC74138_EVT (posedge x[0] or negedge x[0] or \
                         posedge x[1] or negedge x[1] or \
                         posedge x[2] or negedge x[2] or \
                         posedge g1   or negedge g1   or \
                         posedge g2a_n or negedge g2a_n or \
                         posedge g2b_n or negedge g2b_n)

  // If inputs are known and decoder disabled, all outputs must be 1
  assert property (@(`DEC74138_EVT)
    !$isunknown({x,g1,g2a_n,g2b_n}) && !en |-> (y == 8'hFF)
  );

  // If inputs are known and decoder enabled, y must be active-low one-hot by x
  assert property (@(`DEC74138_EVT)
    !$isunknown({x,g1,g2a_n,g2b_n}) && en |-> (y == ~(8'b0000_0001 << x))
  );

  // Outputs must not become X/Z when inputs are known
  assert property (@(`DEC74138_EVT)
    !$isunknown({x,g1,g2a_n,g2b_n}) |-> !$isunknown(y)
  );

  // Functional coverage: hit each decoded value when enabled
  genvar i;
  for (i=0; i<8; i++) begin : COV_DECODE
    localparam logic [2:0] IDX = i[2:0];
    cover property (@(`DEC74138_EVT)
      en && (x == IDX) && (y == ~(8'b0000_0001 << IDX))
    );
  end

  // Coverage: each independent disable cause forces all-ones output
  cover property (@(`DEC74138_EVT) !g1   && ~g2a_n && ~g2b_n && (y==8'hFF));
  cover property (@(`DEC74138_EVT) g2a_n &&  g1    && ~g2b_n && (y==8'hFF));
  cover property (@(`DEC74138_EVT) g2b_n &&  g1    && ~g2a_n && (y==8'hFF));

  `undef DEC74138_EVT
endmodule

// Bind into the DUT
bind decoder_74138_dataflow decoder_74138_sva u_decoder_74138_sva (
  .x(x), .g1(g1), .g2a_n(g2a_n), .g2b_n(g2b_n), .y(y)
);