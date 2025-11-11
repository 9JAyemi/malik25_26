// SVA checker for lab4_3_1
module lab4_3_1_sva (
  input  logic       clk,
  input  logic       m,
  input  logic [3:0] Z,
  input  logic [1:0] state,
  input  logic [1:0] nextstate
);

  localparam logic [1:0] S0 = 2'b00, S1 = 2'b01, S2 = 2'b11, S3 = 2'b10;

  default clocking cb @(posedge clk); endclocking

  function automatic logic [1:0] nxt(input logic [1:0] s);
    unique case (s)
      S0: nxt = S1;
      S1: nxt = S2;
      S2: nxt = S3;
      S3: nxt = S0;
      default: nxt = S0;
    endcase
  endfunction

  // Power-on init
  initial assert (state == S0) else $error("state not initialized to S0");

  // Legal encodings
  a_legal_state:    assert property (state     inside {S0,S1,S2,S3});
  a_legal_nextstate:assert property (nextstate inside {S0,S1,S2,S3});

  // Combinational nextstate mapping
  a_next_comb: assert property (nextstate == nxt(state));

  // Registered update uses previous nextstate
  a_state_from_next: assert property (!$isunknown($past(nextstate))) |-> (state == $past(nextstate));

  // Ring progression each cycle
  a_ring: assert property (!$isunknown($past(state))) |-> (state == nxt($past(state)));

  // One-hot output
  a_onehot_Z: assert property ($onehot(Z));

  // Z values for each state (sampled 1 cycle after state change)
  a_Z_S0: assert property (state == S0 |=> (Z == 4'b0001));
  a_Z_S2: assert property (state == S2 |=> (Z == 4'b0100));
  a_Z_S1: assert property (state == S1 |=> (Z == ($past(m) ? 4'b0010 : 4'b1000)));
  a_Z_S3: assert property (state == S3 |=> (Z == ($past(m) ? 4'b1000 : 4'b0010)));

  // Z changes only when state changes (at clock boundaries)
  a_Z_change_implies_state_change: assert property ((Z != $past(Z)) |-> (state != $past(state)));

  // Coverage
  c_full_ring: cover property (state==S0 ##1 state==S1 ##1 state==S2 ##1 state==S3 ##1 state==S0);
  c_S1_both:   cover property (state==S1 ##1 (Z==4'b0010)) and
                cover property (state==S1 ##1 (Z==4'b1000));
  c_S3_both:   cover property (state==S3 ##1 (Z==4'b1000)) and
                cover property (state==S3 ##1 (Z==4'b0010));

endmodule

// Bind into the DUT
bind lab4_3_1 lab4_3_1_sva sva_i (
  .clk(clk),
  .m(m),
  .Z(Z),
  .state(state),
  .nextstate(nextstate)
)