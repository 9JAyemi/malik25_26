// SVA for ng_INP
module ng_INP_sva (
  input logic        CLK2,
  input logic        NSA,
  input logic [4:0]  Keypad,
  input logic        Keyready,
  input logic [15:0] INP_BUS,
  input logic        KeyStrobe
);

  default clocking cb @(posedge CLK2); endclocking

  // Guard for $past($past(...))
  logic [1:0] init;
  always_ff @(posedge CLK2) init <= {init[0], 1'b1};

  // INP_BUS encoding checks
  a_const_fields: assert property (INP_BUS[15:14] == 2'b00 && INP_BUS[12:5] == 8'h00);
  a_nsa_field:    assert property (INP_BUS[13] === !NSA);
  a_kp_field:     assert property (INP_BUS[4:0]  === Keypad);

  // KeyStrobe is exactly one-cycle delayed rising-edge detect of Keyready
  a_strobe_equiv: assert property (disable iff (!init[1])
                                   KeyStrobe === ($past(Keyready) && !$past($past(Keyready))));
  // Redundant direction (helps debug)
  a_rise_to_strobe: assert property ($rose(Keyready) |=> KeyStrobe);

  // Coverage
  c_strobe:      cover property ($rose(Keyready) ##1 KeyStrobe);
  c_two_strobes: cover property ($rose(Keyready) ##1 KeyStrobe ##[2:$] $rose(Keyready) ##1 KeyStrobe);
  c_nsa0:        cover property (INP_BUS[13] == 1'b0);
  c_nsa1:        cover property (INP_BUS[13] == 1'b1);
  c_kp_min:      cover property (Keypad == 5'h00);
  c_kp_max:      cover property (Keypad == 5'h1F);

endmodule

// Bind to DUT
bind ng_INP ng_INP_sva u_ng_INP_sva (
  .CLK2(CLK2),
  .NSA(NSA),
  .Keypad(Keypad),
  .Keyready(Keyready),
  .INP_BUS(INP_BUS),
  .KeyStrobe(KeyStrobe)
);