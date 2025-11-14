// SVA for mm. Bind this module to mm and connect a sampling clock.
// Example: bind mm mm_sva u_mm_sva(.clk(tb_clk), .addr(addr), .mod(mod), .eff_addr(eff_addr));

module mm_sva(input logic clk,
              input logic [31:0] addr,
              input logic [7:0]  mod,
              input logic [31:0] eff_addr);

  default clocking @(posedge clk); endclocking

  // Decode predicates
  logic is_000, is_10;
  logic is_f00, is_f01, is_f02, is_f03, is_f04, is_f05, is_f06, is_f07, is_f08, is_f0a;

  assign is_000 = (addr[31:20] == 12'h000);
  assign is_10  = (addr[31:24] == 8'h10);
  assign is_f00 = (addr[31:20] == 12'hf00);
  assign is_f01 = (addr[31:20] == 12'hf01);
  assign is_f02 = (addr[31:20] == 12'hf02);
  assign is_f03 = (addr[31:20] == 12'hf03);
  assign is_f04 = (addr[31:20] == 12'hf04);
  assign is_f05 = (addr[31:20] == 12'hf05);
  assign is_f06 = (addr[31:20] == 12'hf06);
  assign is_f07 = (addr[31:20] == 12'hf07);
  assign is_f08 = (addr[31:20] == 12'hf08);
  assign is_f0a = (addr[31:20] == 12'hf0a);

  wire nz_hit = is_10 | is_f00 | is_f01 | is_f02 | is_f03 | is_f04 | is_f05 | is_f06 | is_f07 | is_f08 | is_f0a;

  // Sanity: mapping predicates are mutually exclusive (0 or 1 true at a time)
  assert property ($onehot0({is_10,is_f00,is_f01,is_f02,is_f03,is_f04,is_f05,is_f06,is_f07,is_f08,is_f0a}));

  // Forward mapping: address -> mod
  assert property (is_000 |-> mod == 8'h00);
  assert property (is_10  |-> mod == 8'h01);
  assert property (is_f00 |-> mod == 8'h02);
  assert property (is_f01 |-> mod == 8'h03);
  assert property (is_f02 |-> mod == 8'h04);
  assert property (is_f03 |-> mod == 8'h05);
  assert property (is_f04 |-> mod == 8'h06);
  assert property (is_f05 |-> mod == 8'h07);
  assert property (is_f06 |-> mod == 8'h08);
  assert property (is_f07 |-> mod == 8'h0A);
  assert property (is_f08 |-> mod == 8'h0B);
  assert property (is_f0a |-> mod == 8'h09);
  assert property ((!is_000 && !nz_hit) |-> mod == 8'h00);

  // Reverse mapping: mod -> address class
  assert property (mod == 8'h01 |-> is_10);
  assert property (mod == 8'h02 |-> is_f00);
  assert property (mod == 8'h03 |-> is_f01);
  assert property (mod == 8'h04 |-> is_f02);
  assert property (mod == 8'h05 |-> is_f03);
  assert property (mod == 8'h06 |-> is_f04);
  assert property (mod == 8'h07 |-> is_f05);
  assert property (mod == 8'h08 |-> is_f06);
  assert property (mod == 8'h0A |-> is_f07);
  assert property (mod == 8'h0B |-> is_f08);
  assert property (mod == 8'h09 |-> is_f0a);
  // For mod==0, ensure no non-zero map predicate holds (allows is_000 or default)
  assert property (mod == 8'h00 |-> !nz_hit);

  // Mod range
  assert property (mod inside {8'h00,8'h01,8'h02,8'h03,8'h04,8'h05,8'h06,8'h07,8'h08,8'h09,8'h0A,8'h0B});

  // Effective address transformation
  assert property (mod == 8'h01 |-> eff_addr == {8'h00, addr[23:0]});
  assert property (mod != 8'h01 |-> eff_addr == {12'h000, addr[19:0]});

  // No X on outputs
  assert property (!$isunknown(mod) && !$isunknown(eff_addr));

  // Coverage: hit every class and both eff_addr branches
  cover property (is_000 && mod == 8'h00);
  cover property (is_10  && mod == 8'h01);
  cover property (is_f00 && mod == 8'h02);
  cover property (is_f01 && mod == 8'h03);
  cover property (is_f02 && mod == 8'h04);
  cover property (is_f03 && mod == 8'h05);
  cover property (is_f04 && mod == 8'h06);
  cover property (is_f05 && mod == 8'h07);
  cover property (is_f06 && mod == 8'h08);
  cover property (is_f07 && mod == 8'h0A);
  cover property (is_f08 && mod == 8'h0B);
  cover property (is_f0a && mod == 8'h09);
  cover property (!is_000 && !nz_hit && mod == 8'h00); // default-to-0 case
  cover property (mod == 8'h01 && eff_addr == {8'h00, addr[23:0]});
  cover property (mod != 8'h01 && eff_addr == {12'h000, addr[19:0]});

endmodule