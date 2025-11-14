// SVA checker bound into the DUT; focuses on combinational correctness, overflow/truncation, and end-to-end equivalence.
bind operation_block operation_block_sva sva_inst (.*);

module operation_block_sva (
  input  logic [31:0] i_data0,
  input  logic [31:0] o_data0,
  input  logic [31:0] w1,
  input  logic [31:0] w2048,
  input  logic [31:0] w2047,
  input  logic [31:0] w4,
  input  logic [31:0] w2043,
  input  logic [31:0] w32,
  input  logic [31:0] w2011,
  input  logic [31:0] w32176,
  input  logic [31:0] w30165
);

  // Utility
  function automatic logic [31:0] mul32 (input logic [31:0] a, b);
    mul32 = (a * b)[31:0];
  endfunction

  event comb_ev;
  always @* -> comb_ev;

  let known_i = !$isunknown(i_data0);

  // No-X propagation when input is known
  assert property (@(comb_ev) known_i |-> !$isunknown({w1,w2048,w2047,w4,w2043,w32,w2011,w32176,w30165,o_data0}));

  // Primitive operations
  assert property (@(comb_ev) known_i |-> w1     == (i_data0 << 11));
  assert property (@(comb_ev) known_i |-> w2048  == (i_data0 * 32'd2048)[31:0]);
  assert property (@(comb_ev) known_i |-> w4     == (i_data0 << 2));
  assert property (@(comb_ev) known_i |-> w32    == (i_data0 << 5));

  // Equivalences and chain relationships
  assert property (@(comb_ev) known_i |-> w2048  == w1);                // mul by 2048 == << 11 (mod 32)
  assert property (@(comb_ev) known_i |-> w2047  == w2048 - w1);        // definition
  assert property (@(comb_ev) known_i |-> w2047  == 32'd0);             // must cancel
  assert property (@(comb_ev) known_i |-> w2043  == w2047 - w4);        // definition
  assert property (@(comb_ev) known_i |-> w2043  == -w4);               // simplifies
  assert property (@(comb_ev) known_i |-> w2011  == w2043 - w32);       // definition
  assert property (@(comb_ev) known_i |-> w2011  == -(w4 + w32));       // simplifies
  assert property (@(comb_ev) known_i |-> w32176 == (w2011 << 4));
  assert property (@(comb_ev) known_i |-> w30165 == w32176 - w2011);
  assert property (@(comb_ev) known_i |-> o_data0 == w30165);

  // End-to-end closed-form: o = i * 0xFFFFFDE4  (i * (-540) mod 2^32)
  assert property (@(comb_ev) known_i |-> o_data0 == mul32(i_data0, 32'hFFFFFDE4));
  // Also consistent with 15*w2011
  assert property (@(comb_ev) known_i |-> o_data0 == mul32(w2011, 32'd15));

  // Targeted functional coverage
  cover property (@(comb_ev) known_i && (i_data0 == 32'd0));
  cover property (@(comb_ev) known_i && (i_data0 == 32'hFFFF_FFFF));
  cover property (@(comb_ev) known_i && i_data0[31]);                    // MSB set
  cover property (@(comb_ev) known_i && (|i_data0[31:21]));              // <<11 overflow potential
  cover property (@(comb_ev) known_i && (|i_data0[31:5]));               // <<5 overflow potential
  cover property (@(comb_ev) known_i && (|i_data0[31:2]));               // <<2 overflow potential
  cover property (@(comb_ev) known_i && (o_data0 == 32'd0) && (i_data0 != 32'd0)); // modular zero (i multiple of 2^30)
  cover property (@(comb_ev) known_i && ({1'b0,w4} + {1'b0,w32})[32]);   // sum(w4,w32) carry-out

endmodule