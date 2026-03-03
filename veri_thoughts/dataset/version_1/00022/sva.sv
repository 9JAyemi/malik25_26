// SVA for keypad_left_shift
// Bind-only; checks decode, rotate, onehot, and X-free behavior via ports
module keypad_left_shift_sva (
  input logic        clk,
  input logic [3:0]  col,
  input logic [7:0]  out
);
  // Establish history
  logic init, init2;
  always_ff @(posedge clk) begin
    init  <= 1'b1;
    init2 <= init;
  end

  // Decoder mapping into out[3:0] (1-cycle latency)
  property p_map(input logic [3:0] cin, input logic [3:0] kout);
    @(posedge clk) disable iff(!init) (col == cin) |=> (out[3:0] == kout);
  endproperty
  a_map_1110: assert property (p_map(4'b1110, 4'b0001));
  a_map_1101: assert property (p_map(4'b1101, 4'b0010));
  a_map_1011: assert property (p_map(4'b1011, 4'b0100));
  a_map_0111: assert property (p_map(4'b0111, 4'b1000));
  a_map_else: assert property (@(posedge clk) disable iff(!init)
                               !(col inside {4'b1110,4'b1101,4'b1011,4'b0111}) |=> (out[3:0] == 4'b0000));

  // Upper nibble is left-rotate of prior lower nibble (pipeline relation)
  a_rotate: assert property (@(posedge clk) disable iff(!init)
                             out[7:4] == { $past(out[3:0])[2:0], $past(out[3:0])[3] });

  // Sanity: each nibble is onehot-or-zero
  a_onehot_low:  assert property (@(posedge clk) disable iff(!init)  $onehot0(out[3:0]));
  a_onehot_high: assert property (@(posedge clk) disable iff(!init)  $onehot0(out[7:4]));

  // Knownness after pipeline fills
  a_known_out: assert property (@(posedge clk) disable iff(!init2)  !$isunknown(out));

  // Covers: hit each decode and observe downstream rotate through out
  c_1110: cover property (@(posedge clk) disable iff(!init)
                          (col==4'b1110) |=> (out[3:0]==4'b0001) ##1 (out[7:4]==4'b0010));
  c_1101: cover property (@(posedge clk) disable iff(!init)
                          (col==4'b1101) |=> (out[3:0]==4'b0010) ##1 (out[7:4]==4'b0100));
  c_1011: cover property (@(posedge clk) disable iff(!init)
                          (col==4'b1011) |=> (out[3:0]==4'b0100) ##1 (out[7:4]==4'b1000));
  c_0111: cover property (@(posedge clk) disable iff(!init)
                          (col==4'b0111) |=> (out[3:0]==4'b1000) ##1 (out[7:4]==4'b0001));
  c_else: cover property (@(posedge clk) disable iff(!init)
                          !(col inside {4'b1110,4'b1101,4'b1011,4'b0111}) |=> (out[3:0]==4'b0000));
endmodule

// Bind into the DUT type
bind keypad_left_shift keypad_left_shift_sva u_keypad_left_shift_sva (.clk(clk), .col(col), .out(out));